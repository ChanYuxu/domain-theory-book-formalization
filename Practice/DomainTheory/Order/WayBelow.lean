import Practice.DomainTheory.Order.DCPO.Basic

/-!
# Chapter 2 way-below relation and bases

The way-below relation, compact elements, approximation bases, and
continuous/algebraic domain predicates used in Chapter 2.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w

namespace AbramskyJung
namespace Chapter2

section WayBelowAndBases

variable {α : Type u} [Preorder α]

/-- Definition 2.2.1: the way-below/order-of-approximation relation. -/
def WayBelow (x y : α) : Prop :=
  ∀ ⦃A : Set α⦄ ⦃s : α⦄,
    DirectedSet A → IsSup A s → y ≤ s → ∃ a ∈ A, x ≤ a

infix:50 " ≪ " => WayBelow

/-- Definition 2.2.1: compact elements. -/
def Compact (x : α) : Prop :=
  x ≪ x

/-- `↓↓x`, the set of elements way below `x`. -/
def wayBelowLower (x : α) : Set α :=
  {y | y ≪ x}

/-- `↑↑x`, the set of elements above `x` in the way-below relation. -/
def wayBelowUpper (x : α) : Set α :=
  {y | x ≪ y}

/-- `K(D)`, the set of compact elements. -/
def CompactSet : Set α :=
  {x | Compact x}

/-- Definition 2.2.1: membership in `↓↓x` unfolds to way-below. -/
theorem mem_wayBelowLower {x y : α} :
    y ∈ wayBelowLower x ↔ y ≪ x := by
  rfl

/-- Definition 2.2.1: membership in `↑↑x` unfolds to way-above. -/
theorem mem_wayBelowUpper {x y : α} :
    y ∈ wayBelowUpper x ↔ x ≪ y := by
  rfl

/-- Definition 2.2.1: membership in `K(D)` unfolds to compactness. -/
theorem mem_CompactSet {x : α} :
    x ∈ (CompactSet : Set α) ↔ Compact x := by
  rfl

/-- Definition 2.2.1: compactness means self-approximation. -/
theorem Compact.wayBelow_self {x : α} (hx : Compact x) : x ≪ x :=
  hx

/-- Proposition 2.2.2(1): way-below implies below. -/
theorem prop_2_2_2_1 {x y : α} (h : x ≪ y) : x ≤ y := by
  rcases h (A := ({y} : Set α)) (s := y) (directed_singleton y) (isSup_singleton y) le_rfl with
    ⟨a, ha, hxa⟩
  have hay : a = y := by simpa using ha
  simpa [hay] using hxa

/-- Proposition 2.2.2(2): monotonicity of way-below in both arguments. -/
theorem prop_2_2_2_2 {x x' y y' : α}
    (hx : x' ≤ x) (hxy : x ≪ y) (hy : y ≤ y') : x' ≪ y' := by
  intro A s hdir hsup hys
  rcases hxy hdir hsup (le_trans hy hys) with ⟨a, ha, hxa⟩
  exact ⟨a, ha, le_trans hx hxa⟩

/-- Definition 2.2.3: basis approximants relative to a candidate basis `B`. -/
def Approximants (B : Set α) (x : α) : Set α :=
  {b | b ∈ B ∧ b ≪ x}

/-- Definition 2.2.3, literal version: for every `x`, some directed subset of
    relative approximants has supremum `x`. -/
def IsBasisRaw (B : Set α) : Prop :=
  ∀ x : α, ∃ A : Set α, A ⊆ Approximants B x ∧ DirectedSet A ∧ IsSup A x

/-- Proposition 2.2.4(1) packaged as a stronger basis predicate. -/
def IsBasis (B : Set α) : Prop :=
  ∀ x : α, DirectedSet (Approximants B x) ∧ IsSup (Approximants B x) x

/-- A strong basis is a raw basis. -/
theorem basis_to_raw {B : Set α} (hB : IsBasis B) : IsBasisRaw B := by
  intro x
  exact ⟨Approximants B x, by intro a ha; exact ha, (hB x).1, (hB x).2⟩

/-- Proposition 2.2.4(1): from the literal basis definition, all relative
    approximants form a directed set with supremum `x`. -/
theorem prop_2_2_4_1 {B : Set α} (hB : IsBasisRaw B) : IsBasis B := by
  intro x
  rcases hB x with ⟨A, hAsub, hAdir, hAsup⟩
  constructor
  · constructor
    · rcases hAdir.1 with ⟨a, ha⟩
      exact ⟨a, hAsub ha⟩
    · intro b hb c hc
      rcases hb with ⟨hbB, hbwx⟩
      rcases hc with ⟨hcB, hcwx⟩
      rcases hbwx hAdir hAsup le_rfl with ⟨a, ha, hba⟩
      rcases hcwx hAdir hAsup le_rfl with ⟨a', ha', hca'⟩
      rcases hAdir.2 (x := a) ha (y := a') ha' with ⟨z, hz, haz, ha'z⟩
      exact ⟨z, hAsub hz, le_trans hba haz, le_trans hca' ha'z⟩
  · constructor
    · intro b hb
      exact prop_2_2_2_1 hb.2
    · intro y hy
      exact hAsup.2 y (by
        intro a ha
        exact hy (hAsub ha))

/-- Proposition 2.2.4(3): a superset of a basis is a basis. -/
theorem prop_2_2_4_3 {B C : Set α}
    (hB : IsBasisRaw B) (hBC : B ⊆ C) : IsBasisRaw C := by
  intro x
  rcases hB x with ⟨A, hAsub, hAdir, hAsup⟩
  refine ⟨A, ?_, hAdir, hAsup⟩
  intro a ha
  rcases hAsub ha with ⟨haB, hawx⟩
  exact ⟨hBC haB, hawx⟩

/-- Corollary 2.2.5(1): if a dcpo has a basis, the whole carrier is also a basis. -/
theorem cor_2_2_5_1 {B : Set α} (hB : IsBasisRaw B) :
    IsBasisRaw (Set.univ : Set α) := by
  exact prop_2_2_4_3 hB (by intro x hx; trivial)

/-- A smallest basis is a basis contained in every other basis. -/
def IsSmallestBasisRaw (B : Set α) : Prop :=
  IsBasisRaw B ∧ ∀ C : Set α, IsBasisRaw C → B ⊆ C

/-- The basis-existence component of continuity, generalized to preorders.
Use `IsContinuousDcpo` for Definition 2.2.6 itself. -/
def IsContinuousDomain (α : Type u) [Preorder α] : Prop :=
  ∃ B : Set α, IsBasisRaw B

/-- The compact-basis component of algebraicity, generalized to preorders.
Use `IsAlgebraicDcpo` for Definition 2.2.6 itself. -/
def IsAlgebraicDomain (α : Type u) [Preorder α] : Prop :=
  IsBasisRaw (CompactSet : Set α)

/-- The countable-basis component of omega-continuity. -/
def IsOmegaContinuousDomain (α : Type u) [Preorder α] : Prop :=
  ∃ B : Set α, B.Countable ∧ IsBasisRaw B

/-- The countable compact-basis component of omega-algebraicity. -/
def IsOmegaAlgebraicDomain (α : Type u) [Preorder α] : Prop :=
  (CompactSet : Set α).Countable ∧ IsBasisRaw (CompactSet : Set α)

/-- Definition 2.2.6: continuous dcpos. -/
def IsContinuousDcpo (α : Type u) [Preorder α] : Prop :=
  IsDcpoOrder α ∧ IsContinuousDomain α

/-- Definition 2.2.6: algebraic dcpos. -/
def IsAlgebraicDcpo (α : Type u) [Preorder α] : Prop :=
  IsDcpoOrder α ∧ IsAlgebraicDomain α

/-- Definition 2.2.6: omega-continuous dcpos. -/
def IsOmegaContinuousDcpo (α : Type u) [Preorder α] : Prop :=
  IsDcpoOrder α ∧ IsOmegaContinuousDomain α

/-- Definition 2.2.6: omega-algebraic dcpos. -/
def IsOmegaAlgebraicDcpo (α : Type u) [Preorder α] : Prop :=
  IsDcpoOrder α ∧ IsOmegaAlgebraicDomain α

theorem IsContinuousDcpo.toIsDcpoOrder (h : IsContinuousDcpo α) : IsDcpoOrder α := h.1

theorem IsContinuousDcpo.hasBasis (h : IsContinuousDcpo α) : IsContinuousDomain α := h.2

theorem IsAlgebraicDcpo.toIsDcpoOrder (h : IsAlgebraicDcpo α) : IsDcpoOrder α := h.1

theorem IsAlgebraicDcpo.hasCompactBasis (h : IsAlgebraicDcpo α) : IsAlgebraicDomain α := h.2

/-- Proposition 2.2.7(1): continuous iff the whole set is a basis, i.e. every point is
    the directed supremum of all elements way below it. -/
theorem prop_2_2_7_1 :
    IsContinuousDomain α ↔ IsBasis (Set.univ : Set α) := by
  constructor
  · intro h
    rcases h with ⟨B, hB⟩
    exact prop_2_2_4_1 (cor_2_2_5_1 hB)
  · intro h
    exact ⟨Set.univ, basis_to_raw h⟩

/-- Proposition 2.2.7(2): algebraic iff compact elements form a basis. -/
theorem prop_2_2_7_2 :
    IsAlgebraicDomain α ↔ IsBasisRaw (CompactSet : Set α) := by
  rfl

/-- Proposition 2.2.10: if `B` is a basis, `x ≤ y` implies inclusion of basis
    approximants. -/
theorem prop_2_2_10_forward {B : Set α} {x y : α}
    (hxy : x ≤ y) : Approximants B x ⊆ Approximants B y := by
  intro b hb
  exact ⟨hb.1, prop_2_2_2_2 le_rfl hb.2 hxy⟩

/-- Proposition 2.2.10: if `B` is a basis, then `x ≤ y` iff `B_x ⊆ B_y`. -/
theorem prop_2_2_10_basis_subset {B : Set α} (hB : IsBasis B)
    {x y : α} : x ≤ y ↔ Approximants B x ⊆ Approximants B y := by
  constructor
  · exact prop_2_2_10_forward
  · intro hsub
    exact (hB x).2.2 y (by
      intro b hb
      have hby : b ≪ y := (hsub hb).2
      exact prop_2_2_2_1 hby)

/-- Proposition 2.2.10: if `B` is a basis, then `x ≤ y` iff all basis
    approximants of `x` are below `y`. -/
theorem prop_2_2_10_basis_lower {B : Set α} (hB : IsBasis B)
    {x y : α} : x ≤ y ↔ Approximants B x ⊆ lowerClosure ({y} : Set α) := by
  constructor
  · intro hxy b hb
    exact ⟨y, by simp, le_trans (prop_2_2_2_1 hb.2) hxy⟩
  · intro hsub
    exact (hB x).2.2 y (by
      intro b hb
      rcases hsub hb with ⟨z, hz, hbz⟩
      have hzy : z = y := by simpa using hz
      simpa [hzy] using hbz)

end WayBelowAndBases

section WayBelowAndBasesPartialOrder

variable {α : Type u} [PartialOrder α]

/-- Proposition 2.2.4(2): every basis contains every compact element.
    This theorem is kept in a separate `PartialOrder` section to avoid having two
    unrelated preorder instances in scope. -/
theorem prop_2_2_4_2 {B : Set α}
    (hB : IsBasisRaw B) {c : α} (hc : Compact c) : c ∈ B := by
  rcases hB c with ⟨A, hAsub, hAdir, hAsup⟩
  rcases hc hAdir hAsup le_rfl with ⟨a, ha, hca⟩
  have hac : a ≤ c := prop_2_2_2_1 (hAsub ha).2
  have h_eq : c = a := le_antisymm hca hac
  simpa [h_eq] using (hAsub ha).1

/-- Corollary 2.2.5(2): compact elements are contained in every basis. -/
theorem cor_2_2_5_2_compacts_subset_every_basis {B : Set α}
    (hB : IsBasisRaw B) :
    (CompactSet : Set α) ⊆ B := by
  intro c hc
  exact prop_2_2_4_2 hB hc

/-- Corollary 2.2.5(3): if the compact elements form a basis, they form the
smallest basis. -/
theorem cor_2_2_5_3_compact_basis_smallest
    (hK : IsBasisRaw (CompactSet : Set α)) :
    IsSmallestBasisRaw (CompactSet : Set α) := by
  exact ⟨hK, fun B hB => cor_2_2_5_2_compacts_subset_every_basis hB⟩

/-- Corollary 2.2.5(4): a domain has the compact elements as a smallest basis
exactly when it is algebraic in the current predicate sense. -/
theorem cor_2_2_5_4_smallest_compact_basis_iff_algebraic :
    IsSmallestBasisRaw (CompactSet : Set α) ↔ IsAlgebraicDomain α := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact cor_2_2_5_3_compact_basis_smallest h

end WayBelowAndBasesPartialOrder
end Chapter2
end AbramskyJung

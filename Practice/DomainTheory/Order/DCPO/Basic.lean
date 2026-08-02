import Practice.DomainTheory.Chapter01

/-!
# Chapter 2 order and dcpo core

Core order-theoretic infrastructure used by the Chapter 2 formalization:
upper/lower sets, bounds, directed sets, dcpo-style suprema, Scott-continuity,
and least fixed points.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w

namespace AbramskyJung
namespace Chapter2

section BasicOrder

variable {α : Type u} [Preorder α]

/-- Definition 2.1.3(1): upper sets. -/
def IsUpperSet (A : Set α) : Prop :=
  ∀ ⦃x y : α⦄, x ∈ A → x ≤ y → y ∈ A

/-- Definition 2.1.3(1), dual: lower sets. -/
def IsLowerSet (A : Set α) : Prop :=
  ∀ ⦃x y : α⦄, y ∈ A → x ≤ y → x ∈ A

/-- Upward closure of a set. -/
def upperClosure (A : Set α) : Set α :=
  {y | ∃ x ∈ A, x ≤ y}

/-- Downward closure of a set. -/
def lowerClosure (A : Set α) : Set α :=
  {y | ∃ x ∈ A, y ≤ x}

/-- Definition 2.1.3(2): upper bounds. -/
def IsUpperBound (A : Set α) (x : α) : Prop :=
  ∀ ⦃a : α⦄, a ∈ A → a ≤ x

/-- Definition 2.1.3(2), dual: lower bounds. -/
def IsLowerBound (A : Set α) (x : α) : Prop :=
  ∀ ⦃a : α⦄, a ∈ A → x ≤ a

/-- The set of upper bounds of `A`. -/
def upperBounds (A : Set α) : Set α :=
  {x | IsUpperBound A x}

/-- The set of lower bounds of `A`. -/
def lowerBounds (A : Set α) : Set α :=
  {x | IsLowerBound A x}

/-- Definition 2.1.3(3): maximal elements. -/
def IsMaximal (x : α) : Prop :=
  ∀ ⦃y : α⦄, x ≤ y → y ≤ x

/-- Definition 2.1.3(3), dual: minimal elements. -/
def IsMinimal (x : α) : Prop :=
  ∀ ⦃y : α⦄, y ≤ x → x ≤ y

/-- Definition 2.1.3(3): minimal upper bounds. -/
def IsMinimalUpperBound (A : Set α) (x : α) : Prop :=
  IsUpperBound A x ∧ ∀ ⦃y : α⦄, IsUpperBound A y → y ≤ x → x ≤ y

/-- Definition 2.1.3(4): largest element. -/
def IsLargest (x : α) : Prop :=
  ∀ y : α, y ≤ x

/-- Definition 2.1.3(4): least element/bottom. -/
def IsLeast (x : α) : Prop :=
  ∀ y : α, x ≤ y

/-- Definition 2.1.3(5): supremum/join of a set. -/
def IsSup (A : Set α) (x : α) : Prop :=
  IsUpperBound A x ∧ ∀ y : α, IsUpperBound A y → x ≤ y

/-- Definition 2.1.3(5): infimum/meet of a set. -/
def IsInf (A : Set α) (x : α) : Prop :=
  IsLowerBound A x ∧ ∀ y : α, IsLowerBound A y → y ≤ x

/-- Definition 2.1.3(6): existence of binary joins. -/
def HasBinaryJoins (α : Type u) [Preorder α] : Prop :=
  ∀ x y : α, ∃ z : α, IsSup ({w | w = x ∨ w = y} : Set α) z

/-- Definition 2.1.3(6): existence of binary meets. -/
def HasBinaryMeets (α : Type u) [Preorder α] : Prop :=
  ∀ x y : α, ∃ z : α, IsInf ({w | w = x ∨ w = y} : Set α) z

/-- Definition 2.1.3(6): lattice, formulated by universal binary joins and meets. -/
def IsLatticeOrder (α : Type u) [Preorder α] : Prop :=
  HasBinaryJoins α ∧ HasBinaryMeets α

/-- Definition 2.1.3(6): complete lattice, formulated by all suprema and infima. -/
def IsCompleteOrder (α : Type u) [Preorder α] : Prop :=
  (∀ A : Set α, ∃ x : α, IsSup A x) ∧ (∀ A : Set α, ∃ x : α, IsInf A x)

/-- Definition 2.1.3(1): a set is contained in its upward closure. -/
theorem subset_upperClosure (A : Set α) : A ⊆ upperClosure A := by
  intro x hx
  exact ⟨x, hx, le_rfl⟩

/-- Definition 2.1.3(1), dual: a set is contained in its downward closure. -/
theorem subset_lowerClosure (A : Set α) : A ⊆ lowerClosure A := by
  intro x hx
  exact ⟨x, hx, le_rfl⟩

/-- Definition 2.1.3(1): upward closures are upper sets. -/
theorem isUpperSet_upperClosure (A : Set α) : IsUpperSet (upperClosure A) := by
  intro x y hx hxy
  rcases hx with ⟨a, ha, hax⟩
  exact ⟨a, ha, le_trans hax hxy⟩

/-- Definition 2.1.3(1), dual: downward closures are lower sets. -/
theorem isLowerSet_lowerClosure (A : Set α) : IsLowerSet (lowerClosure A) := by
  intro x y hy hxy
  rcases hy with ⟨a, ha, hya⟩
  exact ⟨a, ha, le_trans hxy hya⟩

/-- Definition 2.1.3(2): membership in `upperBounds` is the upper-bound predicate. -/
theorem mem_upperBounds {A : Set α} {x : α} :
    x ∈ upperBounds A ↔ IsUpperBound A x := by
  rfl

/-- Definition 2.1.3(2), dual: membership in `lowerBounds` is the lower-bound predicate. -/
theorem mem_lowerBounds {A : Set α} {x : α} :
    x ∈ lowerBounds A ↔ IsLowerBound A x := by
  rfl

/-- Definition 2.1.3(4): a largest element is an upper bound for every set. -/
theorem IsLargest.isUpperBound {A : Set α} {x : α}
    (hx : IsLargest x) : IsUpperBound A x := by
  intro a _ha
  exact hx a

/-- Definition 2.1.3(4), dual: a least element is a lower bound for every set. -/
theorem IsLeast.isLowerBound {A : Set α} {x : α}
    (hx : IsLeast x) : IsLowerBound A x := by
  intro a _ha
  exact hx a

theorem IsSup.le_of_isSup {A : Set α} {x y : α}
    (hx : IsSup A x) (hy : IsSup A y) : x ≤ y := by
  exact hx.2 y hy.1

theorem IsInf.le_of_isInf {A : Set α} {x y : α}
    (hx : IsInf A x) (hy : IsInf A y) : y ≤ x := by
  exact hx.2 y hy.1

/-- Proposition 2.1.4(1), supremum part. -/
theorem prop_2_1_4_sup_mono {A B : Set α} {a b : α}
    (hAB : A ⊆ B) (ha : IsSup A a) (hb : IsSup B b) : a ≤ b := by
  exact ha.2 b (by
    intro x hx
    exact hb.1 (hAB hx))

/-- Cofinal subsets have the same supremum as the ambient set. -/
theorem IsSup.of_cofinal_subset {A B : Set α} {s : α}
    (hBA : B ⊆ A) (hcofinal : ∀ a ∈ A, ∃ b ∈ B, a ≤ b)
    (hs : IsSup B s) :
    IsSup A s := by
  constructor
  · intro a ha
    rcases hcofinal a ha with ⟨b, hb, hab⟩
    exact le_trans hab (hs.1 hb)
  · intro y hy
    exact hs.2 y (by
      intro b hb
      exact hy (hBA hb))

/-- Proposition 2.1.15 support: a largest element of an extension with the same
upper bounds is the supremum of the original set.  This is the final order
calculation used in Cohn/Markowsky-style proofs after extending a directed set
to a chain or maximal directed set with unchanged upper bounds. -/
theorem IsSup.of_largest_same_upperBounds {A E : Set α} {s : α}
    (hAE : A ⊆ E) (hsE : s ∈ E)
    (hsGreatest : ∀ ⦃x : α⦄, x ∈ E → x ≤ s)
    (hUpper : ∀ x : α, IsUpperBound A x ↔ IsUpperBound E x) :
    IsSup A s := by
  constructor
  · intro a ha
    exact hsGreatest (hAE ha)
  · intro x hx
    exact (hUpper x).mp hx hsE

/-- Proposition 2.1.4(1), infimum part. -/
theorem prop_2_1_4_inf_mono {A B : Set α} {a b : α}
    (hAB : A ⊆ B) (ha : IsInf A a) (hb : IsInf B b) : b ≤ a := by
  exact ha.2 b (by
    intro x hx
    exact hb.1 (hAB hx))

/-- Proposition 2.1.4(2), supremum is unchanged by taking downward closure. -/
theorem prop_2_1_4_sup_lowerClosure {A : Set α} {s : α}
    (hs : IsSup A s) : IsSup (lowerClosure A) s := by
  constructor
  · intro y hy
    rcases hy with ⟨a, ha, hya⟩
    exact le_trans hya (hs.1 ha)
  · intro z hz
    exact hs.2 z (by
      intro a ha
      exact hz ⟨a, ha, le_rfl⟩)

/-- Proposition 2.1.4(2), infimum is unchanged by taking upward closure. -/
theorem prop_2_1_4_inf_upperClosure {A : Set α} {s : α}
    (hs : IsInf A s) : IsInf (upperClosure A) s := by
  constructor
  · intro y hy
    rcases hy with ⟨a, ha, hay⟩
    exact le_trans (hs.1 ha) hay
  · intro z hz
    exact hs.2 z (by
      intro a ha
      exact hz ⟨a, ha, le_rfl⟩)

/-- Proposition 2.1.4(3), supremum over a union of indexed sets. -/
theorem prop_2_1_4_sup_iUnion {ι : Type v} {A : ι → Set α} {s : ι → α} {t : α}
    (hA : ∀ i : ι, IsSup (A i) (s i))
    (ht : IsSup (Set.range s) t) :
    IsSup (Set.iUnion A) t := by
  constructor
  · intro a ha
    rw [Set.mem_iUnion] at ha
    rcases ha with ⟨i, hai⟩
    exact le_trans ((hA i).1 hai) (ht.1 ⟨i, rfl⟩)
  · intro y hy
    refine ht.2 y ?_
    intro si hsi
    rcases hsi with ⟨i, rfl⟩
    exact (hA i).2 y (by
      intro a ha
      exact hy (by
        rw [Set.mem_iUnion]
        exact ⟨i, ha⟩))

/-- Proposition 2.1.4(3), infimum over a union of indexed sets. -/
theorem prop_2_1_4_inf_iUnion {ι : Type v} {A : ι → Set α} {s : ι → α} {t : α}
    (hA : ∀ i : ι, IsInf (A i) (s i))
    (ht : IsInf (Set.range s) t) :
    IsInf (Set.iUnion A) t := by
  constructor
  · intro a ha
    rw [Set.mem_iUnion] at ha
    rcases ha with ⟨i, hai⟩
    exact le_trans (ht.1 ⟨i, rfl⟩) ((hA i).1 hai)
  · intro y hy
    refine ht.2 y ?_
    intro si hsi
    rcases hsi with ⟨i, rfl⟩
    exact (hA i).2 y (by
      intro a ha
      exact hy (by
        rw [Set.mem_iUnion]
        exact ⟨i, ha⟩))

end BasicOrder

section BasicOrderPartialOrder

variable {α : Type u} [PartialOrder α]

theorem IsSup.unique {A : Set α} {x y : α}
    (hx : IsSup A x) (hy : IsSup A y) : x = y := by
  exact le_antisymm (IsSup.le_of_isSup hx hy) (IsSup.le_of_isSup hy hx)

theorem IsInf.unique {A : Set α} {x y : α}
    (hx : IsInf A x) (hy : IsInf A y) : x = y := by
  exact le_antisymm (IsInf.le_of_isInf hy hx) (IsInf.le_of_isInf hx hy)

end BasicOrderPartialOrder

section ClosureSystems

variable {α : Type u}

/-- Section 2.1.2: closure systems, closed under arbitrary intersections. -/
structure ClosureSystem (α : Type u) where
  closed : Set (Set α)
  sInter_closed : ∀ F : Set (Set α), F ⊆ closed → ⋂₀ F ∈ closed

namespace ClosureSystem

/-- The closure/hull of a subset with respect to a closure system. -/
def closure (C : ClosureSystem α) (A : Set α) : Set α :=
  ⋂₀ {B : Set α | B ∈ C.closed ∧ A ⊆ B}

theorem closure_mem (C : ClosureSystem α) (A : Set α) :
    C.closure A ∈ C.closed := by
  exact C.sInter_closed {B : Set α | B ∈ C.closed ∧ A ⊆ B} (by
    intro B hB
    exact hB.1)

theorem subset_closure (C : ClosureSystem α) {A : Set α} :
    A ⊆ C.closure A := by
  intro x hx B hB
  exact hB.2 hx

theorem closure_least (C : ClosureSystem α) {A B : Set α}
    (hB : B ∈ C.closed) (hAB : A ⊆ B) : C.closure A ⊆ B := by
  intro x hx
  exact hx B ⟨hB, hAB⟩

/-- Proposition 2.1.5, infimum part: intersections give infima by inclusion. -/
theorem isInf_sInter {F : Set (Set α)} :
    IsInf F (⋂₀ F) := by
  constructor
  · intro B hB x hx
    exact hx B hB
  · intro Y hY x hx B hB
    exact hY hB hx

/-- Proposition 2.1.5, supremum part inside a closure system: closure of union is
    the least closed upper bound. -/
theorem closure_sUnion_least_closed_upper_bound
    (C : ClosureSystem α) {F : Set (Set α)} {Z : Set α}
    (hZ : Z ∈ C.closed) (hFZ : ∀ B ∈ F, B ⊆ Z) :
    C.closure (⋃₀ F) ⊆ Z := by
  exact C.closure_least hZ (by
    intro x hx
    rcases hx with ⟨B, hB, hxB⟩
    exact hFZ B hB hxB)

end ClosureSystem

end ClosureSystems

section MonotoneAndDirected

variable {α : Type u} [Preorder α]
variable {β : Type v} [Preorder β]
variable {γ : Type w} [Preorder γ]

/-- Definition 2.1.8: directed subsets. -/
def DirectedSet (A : Set α) : Prop :=
  A.Nonempty ∧ ∀ ⦃x : α⦄, x ∈ A → ∀ ⦃y : α⦄, y ∈ A →
    ∃ z ∈ A, x ≤ z ∧ y ≤ z

/-- Definition 2.1.8: ideals are directed lower sets. -/
def IsIdeal (A : Set α) : Prop :=
  IsLowerSet A ∧ DirectedSet A

/-- Definition 2.1.8, dual: filters are directed upper sets in the opposite order. -/
def IsFilter (A : Set α) : Prop :=
  IsUpperSet A ∧ A.Nonempty ∧ ∀ ⦃x : α⦄, x ∈ A → ∀ ⦃y : α⦄, y ∈ A →
    ∃ z ∈ A, z ≤ x ∧ z ≤ y

/-- Chains in the sense used after Definition 2.1.8. -/
def IsChainSet (A : Set α) : Prop :=
  A.Nonempty ∧ ∀ ⦃x : α⦄, x ∈ A → ∀ ⦃y : α⦄, y ∈ A → x ≤ y ∨ y ≤ x

/-- Definition 2.1.8: principal ideals are ideals. -/
theorem principal_ideal_isIdeal (x : α) : IsIdeal (lowerClosure ({x} : Set α)) := by
  constructor
  · exact isLowerSet_lowerClosure ({x} : Set α)
  · constructor
    · exact ⟨x, ⟨x, by simp, le_rfl⟩⟩
    · intro a ha b hb
      rcases ha with ⟨xa, hxa, hax⟩
      rcases hb with ⟨xb, hxb, hbx⟩
      have hxa_eq : xa = x := by simpa using hxa
      have hxb_eq : xb = x := by simpa using hxb
      refine ⟨x, ⟨x, by simp, le_rfl⟩, ?_, ?_⟩
      · simpa [hxa_eq] using hax
      · simpa [hxb_eq] using hbx

/-- Definition 2.1.8, dual: principal filters are filters. -/
theorem principal_filter_isFilter (x : α) : IsFilter (upperClosure ({x} : Set α)) := by
  constructor
  · exact isUpperSet_upperClosure ({x} : Set α)
  · constructor
    · exact ⟨x, ⟨x, by simp, le_rfl⟩⟩
    · intro a ha b hb
      rcases ha with ⟨xa, hxa, hxa_le⟩
      rcases hb with ⟨xb, hxb, hxb_le⟩
      have hxa_eq : xa = x := by simpa using hxa
      have hxb_eq : xb = x := by simpa using hxb
      refine ⟨x, ⟨x, by simp, le_rfl⟩, ?_, ?_⟩
      · simpa [hxa_eq] using hxa_le
      · simpa [hxb_eq] using hxb_le

/-- A chain, viewed as a subtype, inherits a linear order from the ambient
partial order.  This is a small bridge needed for the Markowsky/cofinality
arguments, where chains are often treated as linearly ordered types. -/
@[reducible]
noncomputable def linearOrderOfChainSet
    {α : Type u} [PartialOrder α] {A : Set α} (hA : IsChainSet A) :
  LinearOrder A := by
  classical
  let r : A → A → Prop := fun x y => x.1 < y.1
  have hSTO : IsStrictTotalOrder A r := {
    toTrichotomous := Std.trichotomous_of_rel_or_eq_or_rel_swap fun {x y} => by
      rcases hA.2 x.2 y.2 with hxy | hyx
      · by_cases hEq : x = y
        · exact Or.inr (Or.inl hEq)
        · have hne : x.1 ≠ y.1 := by
            intro hxyEq
            exact hEq (Subtype.ext hxyEq)
          exact Or.inl (lt_of_le_of_ne hxy hne)
      · by_cases hEq : x = y
        · exact Or.inr (Or.inl hEq)
        · have hne : y.1 ≠ x.1 := by
            intro hyxEq
            exact hEq (Subtype.ext hyxEq.symm)
          exact Or.inr (Or.inr (lt_of_le_of_ne hyx hne))
    irrefl := by
      intro x h
      exact lt_irrefl x.1 h
    trans := by
      intro x y z hxy hyz
      exact lt_trans hxy hyz }
  letI : IsStrictTotalOrder A r := hSTO
  exact linearOrderOfSTO r

theorem directed_singleton (x : α) : DirectedSet ({x} : Set α) := by
  constructor
  · exact ⟨x, by simp⟩
  · intro a ha b hb
    have hax : a = x := by simpa using ha
    have hbx : b = x := by simpa using hb
    refine ⟨x, by simp, ?_, ?_⟩
    · simpa [hax]
    · simpa [hbx]

theorem isSup_singleton (x : α) : IsSup ({x} : Set α) x := by
  constructor
  · intro a ha
    have hax : a = x := by simpa using ha
    simpa [hax]
  · intro y hy
    exact hy (a := x) (by simp)

theorem chain_directed {A : Set α} (hA : IsChainSet A) : DirectedSet A := by
  constructor
  · exact hA.1
  · intro x hx y hy
    rcases hA.2 hx hy with hxy | hyx
    · exact ⟨y, hy, hxy, le_rfl⟩
    · exact ⟨x, hx, le_rfl, hyx⟩

/-- The image of a directed set under a monotone map is directed. -/
theorem DirectedSet.image {A : Set α} {f : α → β}
    (hf : Monotone f) (hA : DirectedSet A) : DirectedSet (f '' A) := by
  constructor
  · rcases hA.1 with ⟨a, ha⟩
    exact ⟨f a, ⟨a, ha, rfl⟩⟩
  · intro x hx y hy
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    rcases hA.2 ha hb with ⟨c, hc, hac, hbc⟩
    exact ⟨f c, ⟨c, hc, rfl⟩, hf hac, hf hbc⟩

/-- A finite subset of a directed set has an upper bound inside the directed set. -/
theorem DirectedSet.exists_upper_finite {A F : Set α}
    (hA : DirectedSet A) (hFfin : F.Finite) (hFsub : F ⊆ A) :
    ∃ z ∈ A, ∀ x ∈ F, x ≤ z := by
  induction F, hFfin using Set.Finite.induction_on with
  | empty =>
      rcases hA.1 with ⟨z, hz⟩
      exact ⟨z, hz, by intro x hx; cases hx⟩
  | @insert a F haF _ ih =>
      have hFsub' : F ⊆ A := by
        intro x hx
        exact hFsub (by simp [hx])
      rcases ih hFsub' with ⟨z, hzA, hzF⟩
      have haA : a ∈ A := hFsub (by simp)
      rcases hA.2 haA hzA with ⟨w, hwA, haw, hzw⟩
      exact ⟨w, hwA, by
        intro x hx
        simp only [Set.mem_insert_iff] at hx
        rcases hx with rfl | hxF
        · exact haw
        · exact le_trans (hzF x hxF) hzw⟩

/-- A finite directed set has a greatest element, hence its own supremum. -/
theorem DirectedSet.exists_isSup_of_finite {A : Set α}
    (hA : DirectedSet A) (hAfin : A.Finite) :
    ∃ z ∈ A, IsSup A z := by
  rcases DirectedSet.exists_upper_finite hA hAfin (by intro x hx; exact hx) with
    ⟨z, hzA, hz⟩
  refine ⟨z, hzA, ?_⟩
  constructor
  · intro x hx
    exact hz x hx
  · intro y hy
    exact hy hzA

/-- A finite family with pointwise upper bounds in a directed set has one common
upper bound in that directed set. -/
theorem DirectedSet.exists_upper_finite_of_forall {A F : Set α}
    (hA : DirectedSet A) (hFfin : F.Finite)
    (hF : ∀ x ∈ F, ∃ a ∈ A, x ≤ a) :
    ∃ z ∈ A, ∀ x ∈ F, x ≤ z := by
  induction F, hFfin using Set.Finite.induction_on with
  | empty =>
      rcases hA.1 with ⟨z, hz⟩
      exact ⟨z, hz, by intro x hx; cases hx⟩
  | @insert a F haF _ ih =>
      rcases hF a (by simp) with ⟨ua, huaA, haua⟩
      have hF' : ∀ x ∈ F, ∃ b ∈ A, x ≤ b := by
        intro x hx
        exact hF x (by simp [hx])
      rcases ih hF' with ⟨uF, huFA, huF⟩
      rcases hA.2 huaA huFA with ⟨z, hzA, huaz, huFz⟩
      exact ⟨z, hzA, by
        intro x hx
        simp only [Set.mem_insert_iff] at hx
        rcases hx with rfl | hxF
        · exact le_trans haua huaz
        · exact le_trans (huF x hxF) huFz⟩

/-- Common upper bounds, inside a directed set, of a finite list of constraints.
This is a reusable finite piece in the Iwamura/Markowsky directed-set
decomposition used for Proposition 2.1.15. -/
def DirectedSet.finsetUpperBounds (A : Set α) (s : Finset α) : Set α :=
  {u | u ∈ A ∧ ∀ x ∈ s, x ≤ u}

theorem DirectedSet.finsetUpperBounds_subset (A : Set α) (s : Finset α) :
    DirectedSet.finsetUpperBounds A s ⊆ A := by
  intro u hu
  exact hu.1

theorem DirectedSet.finsetUpperBounds_nonempty {A : Set α} {s : Finset α}
    (hA : DirectedSet A) (hs : ∀ x ∈ s, x ∈ A) :
    (DirectedSet.finsetUpperBounds A s).Nonempty := by
  rcases DirectedSet.exists_upper_finite hA (Finset.finite_toSet s)
      (by intro x hx; exact hs x hx) with ⟨u, huA, hu⟩
  exact ⟨u, huA, by intro x hx; exact hu x hx⟩

/-- Common upper bounds of finitely many members of a directed set are directed. -/
theorem DirectedSet.finsetUpperBounds_directed {A : Set α} {s : Finset α}
    (hA : DirectedSet A) (hs : ∀ x ∈ s, x ∈ A) :
    DirectedSet (DirectedSet.finsetUpperBounds A s) := by
  constructor
  · exact DirectedSet.finsetUpperBounds_nonempty hA hs
  · intro u hu v hv
    rcases hA.2 hu.1 hv.1 with ⟨w, hwA, huw, hvw⟩
    exact ⟨w, ⟨hwA, by
      intro x hx
      exact le_trans (hu.2 x hx) huw⟩, huw, hvw⟩

/-- Enlarging the finite constraint set shrinks the set of common upper bounds. -/
theorem DirectedSet.finsetUpperBounds_antitone (A : Set α) :
    Antitone (DirectedSet.finsetUpperBounds A) := by
  intro s t hst u hu
  exact ⟨hu.1, by
    intro x hx
    exact hu.2 x (hst hx)⟩

theorem DirectedSet.mem_finsetUpperBounds_singleton {A : Set α} {a : α}
    (ha : a ∈ A) :
    a ∈ DirectedSet.finsetUpperBounds A {a} := by
  exact ⟨ha, by
    intro x hx
    have hxa : x = a := by simpa using hx
    simpa [hxa]⟩

theorem DirectedSet.le_of_mem_finsetUpperBounds {A : Set α} {s : Finset α}
    {u x : α} (hu : u ∈ DirectedSet.finsetUpperBounds A s) (hx : x ∈ s) :
    x ≤ u :=
  hu.2 x hx

/-- Previous choices used when recursively choosing a coherent finite-subset
upper bound. -/
private def DirectedSet.coherentFinsetUpperPrevious
    {I : Type v} [Preorder I] (s : Finset I)
    (rec : ∀ t : Finset I, t ⊂ s → I) : Set I :=
  {x | ∃ (t : Finset I) (ht : t ⊂ s), x = rec t ht}

private theorem DirectedSet.coherentFinsetUpperPrevious_finite
    {I : Type v} [Preorder I] (s : Finset I)
    (rec : ∀ t : Finset I, t ⊂ s → I) :
    (DirectedSet.coherentFinsetUpperPrevious s rec).Finite := by
  classical
  let T : Set (Finset I) := {t | t ⊂ s}
  have hTfin : T.Finite := by
    exact (Finset.finite_toSet s.ssubsets).subset (by
      intro t ht
      exact Finset.mem_ssubsets.mpr ht)
  letI : Fintype {t : Finset I // t ⊂ s} := Set.Finite.fintype hTfin
  let f : {t : Finset I // t ⊂ s} → I := fun t => rec t.1 t.2
  have hprev_eq : DirectedSet.coherentFinsetUpperPrevious s rec = Set.range f := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
    · intro hx
      rcases hx with ⟨t, rfl⟩
      exact ⟨t.1, t.2, rfl⟩
  rw [hprev_eq]
  exact Set.finite_range f

private def DirectedSet.coherentFinsetUpperConstraints
    {I : Type v} [Preorder I] (s : Finset I)
    (rec : ∀ t : Finset I, t ⊂ s → I) : Set I :=
  (s : Set I) ∪ DirectedSet.coherentFinsetUpperPrevious s rec

private theorem DirectedSet.coherentFinsetUpperConstraints_finite
    {I : Type v} [Preorder I] (s : Finset I)
    (rec : ∀ t : Finset I, t ⊂ s → I) :
    (DirectedSet.coherentFinsetUpperConstraints s rec).Finite :=
  (Finset.finite_toSet s).union
    (DirectedSet.coherentFinsetUpperPrevious_finite s rec)

/-- A coherent choice of upper bounds for finite subsets of a directed set:
proper-subset choices are included among the finite constraints for the next
choice, so the resulting map is monotone for subset inclusion. -/
private noncomputable def DirectedSet.coherentFinsetUpperStep
    {I : Type v} [Preorder I] (hI : DirectedSet (Set.univ : Set I))
    (s : Finset I) (rec : ∀ t : Finset I, t ⊂ s → I) : I :=
  Classical.choose (DirectedSet.exists_upper_finite hI
    (DirectedSet.coherentFinsetUpperConstraints_finite s rec)
    (by intro x _hx; exact trivial))

private theorem DirectedSet.coherentFinsetUpperStep_spec
    {I : Type v} [Preorder I] (hI : DirectedSet (Set.univ : Set I))
    (s : Finset I) (rec : ∀ t : Finset I, t ⊂ s → I) :
    (∀ i ∈ s, i ≤ DirectedSet.coherentFinsetUpperStep hI s rec) ∧
      ∀ t : Finset I, ∀ ht : t ⊂ s,
        rec t ht ≤ DirectedSet.coherentFinsetUpperStep hI s rec := by
  classical
  have hspec := Classical.choose_spec
    (DirectedSet.exists_upper_finite hI
      (DirectedSet.coherentFinsetUpperConstraints_finite s rec)
      (by intro x _hx; exact trivial))
  constructor
  · intro i hi
    exact hspec.2 i (Or.inl hi)
  · intro t ht
    exact hspec.2 (rec t ht) (Or.inr ⟨t, ht, rfl⟩)

/-- Coherent upper-bound choice for finite subsets of a directed set. -/
noncomputable def DirectedSet.coherentFinsetUpper
    {I : Type v} [Preorder I] (hI : DirectedSet (Set.univ : Set I)) :
    Finset I → I :=
  Finset.strongInduction fun s rec =>
    DirectedSet.coherentFinsetUpperStep hI s rec

theorem DirectedSet.le_coherentFinsetUpper_of_mem
    {I : Type v} [Preorder I] (hI : DirectedSet (Set.univ : Set I))
    {s : Finset I} {i : I} (hi : i ∈ s) :
    i ≤ DirectedSet.coherentFinsetUpper hI s := by
  rw [show DirectedSet.coherentFinsetUpper hI s =
      DirectedSet.coherentFinsetUpperStep hI s
        (fun t _ht => DirectedSet.coherentFinsetUpper hI t) by
    rw [DirectedSet.coherentFinsetUpper, Finset.strongInduction_eq]]
  exact (DirectedSet.coherentFinsetUpperStep_spec hI s
    (fun t _ht => DirectedSet.coherentFinsetUpper hI t)).1 i hi

theorem DirectedSet.coherentFinsetUpper_mono
    {I : Type v} [Preorder I] (hI : DirectedSet (Set.univ : Set I)) :
    Monotone (DirectedSet.coherentFinsetUpper hI) := by
  intro s t hst
  by_cases hEq : s = t
  · simpa [hEq]
  · have hssub : s ⊂ t := Finset.ssubset_iff_subset_ne.mpr ⟨hst, hEq⟩
    rw [show DirectedSet.coherentFinsetUpper hI t =
        DirectedSet.coherentFinsetUpperStep hI t
          (fun r _hr => DirectedSet.coherentFinsetUpper hI r) by
      rw [DirectedSet.coherentFinsetUpper, Finset.strongInduction_eq]]
    exact (DirectedSet.coherentFinsetUpperStep_spec hI t
      (fun r _hr => DirectedSet.coherentFinsetUpper hI r)).2 s hssub

/-- A recursive chain of upper bounds for a sequence in a directed set. -/
noncomputable def DirectedSet.cumulativeUpperSub {A : Set α}
    (hA : DirectedSet A) (u : Nat → α) (hu : ∀ n : Nat, u n ∈ A) :
    Nat → {x : α // x ∈ A}
  | 0 => ⟨u 0, hu 0⟩
  | n + 1 =>
      let hw := hA.2
        (x := (DirectedSet.cumulativeUpperSub hA u hu n).1)
        (DirectedSet.cumulativeUpperSub hA u hu n).2
        (y := u (n + 1)) (hu (n + 1))
      ⟨Classical.choose hw, (Classical.choose_spec hw).1⟩

/-- The underlying sequence of cumulative upper bounds. -/
noncomputable def DirectedSet.cumulativeUpper {A : Set α}
    (hA : DirectedSet A) (u : Nat → α) (hu : ∀ n : Nat, u n ∈ A) :
    Nat → α :=
  fun n => (DirectedSet.cumulativeUpperSub hA u hu n).1

theorem DirectedSet.cumulativeUpper_mem {A : Set α}
    (hA : DirectedSet A) (u : Nat → α) (hu : ∀ n : Nat, u n ∈ A)
    (n : Nat) :
    DirectedSet.cumulativeUpper hA u hu n ∈ A :=
  (DirectedSet.cumulativeUpperSub hA u hu n).2

theorem DirectedSet.cumulativeUpper_mono_step {A : Set α}
    (hA : DirectedSet A) (u : Nat → α) (hu : ∀ n : Nat, u n ∈ A)
    (n : Nat) :
    DirectedSet.cumulativeUpper hA u hu n ≤
      DirectedSet.cumulativeUpper hA u hu (n + 1) := by
  unfold DirectedSet.cumulativeUpper
  let hw := hA.2
    (x := (DirectedSet.cumulativeUpperSub hA u hu n).1)
    (DirectedSet.cumulativeUpperSub hA u hu n).2
    (y := u (n + 1)) (hu (n + 1))
  change (DirectedSet.cumulativeUpperSub hA u hu n).1 ≤ Classical.choose hw
  exact (Classical.choose_spec hw).2.1

theorem DirectedSet.le_cumulativeUpper_self {A : Set α}
    (hA : DirectedSet A) (u : Nat → α) (hu : ∀ n : Nat, u n ∈ A)
    (n : Nat) :
    u n ≤ DirectedSet.cumulativeUpper hA u hu n := by
  cases n with
  | zero =>
      simp [DirectedSet.cumulativeUpper, DirectedSet.cumulativeUpperSub]
  | succ n =>
      unfold DirectedSet.cumulativeUpper
      let hw := hA.2
        (x := (DirectedSet.cumulativeUpperSub hA u hu n).1)
        (DirectedSet.cumulativeUpperSub hA u hu n).2
        (y := u (n + 1)) (hu (n + 1))
      change u (n + 1) ≤ Classical.choose hw
      exact (Classical.choose_spec hw).2.2

theorem DirectedSet.cumulativeUpper_monotone {A : Set α}
    (hA : DirectedSet A) (u : Nat → α) (hu : ∀ n : Nat, u n ∈ A) :
    Monotone (DirectedSet.cumulativeUpper hA u hu) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base =>
      exact le_rfl
  | succ k _ ih =>
      exact le_trans ih (DirectedSet.cumulativeUpper_mono_step hA u hu k)

/-- Antisymmetry as a proposition over an existing preorder.  This keeps the
book-facing partial-order condition explicit without installing a competing
order instance. -/
def IsAntisymmetricOrder (α : Type u) [Preorder α] : Prop :=
  ∀ x y : α, x ≤ y → y ≤ x → x = y

/-- Directed completeness of a preorder: every nonempty directed set has a
supremum.  This is the order-completeness component reused throughout the
development; `IsDcpoOrder` adds the antisymmetry required by the book's notion
of a dcpo. -/
def IsDcpo (α : Type u) [Preorder α] : Prop :=
  ∀ A : Set α, DirectedSet A → ∃ x : α, IsSup A x

/-- Definition 2.1.13: a directed-complete partial order, represented over a
preorder by directed completeness together with antisymmetry. -/
def IsDcpoOrder (α : Type u) [Preorder α] : Prop :=
  IsDcpo α ∧ IsAntisymmetricOrder α

theorem IsDcpoOrder.directedComplete (h : IsDcpoOrder α) : IsDcpo α := h.1

theorem IsDcpoOrder.antisymmetric (h : IsDcpoOrder α) : IsAntisymmetricOrder α := h.2

/-- Definition 2.1.17: Scott-continuous maps, formulated by preservation of
    directed suprema. -/
def ScottContinuous (f : α → β) : Prop :=
  Monotone f ∧ ∀ ⦃A : Set α⦄ ⦃x : α⦄,
    DirectedSet A → IsSup A x → IsSup (f '' A) (f x)

theorem ScottContinuous.monotone {f : α → β} (hf : ScottContinuous f) :
    Monotone f := hf.1

theorem ScottContinuous.image_directed {f : α → β} (hf : ScottContinuous f)
    {A : Set α} (hA : DirectedSet A) :
    DirectedSet (f '' A) :=
  DirectedSet.image hf.1 hA

theorem ScottContinuous.maps_isSup {f : α → β} (hf : ScottContinuous f)
    {A : Set α} {x : α} (hA : DirectedSet A) (hx : IsSup A x) :
    IsSup (f '' A) (f x) :=
  hf.2 hA hx

theorem scottContinuous_id : ScottContinuous (fun x : α => x) := by
  constructor
  · intro x y hxy
    exact hxy
  · intro A x hA hx
    simpa using hx

theorem ScottContinuous.comp {f : β → γ} {g : α → β}
    (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous (fun x : α => f (g x)) := by
  constructor
  · intro x y hxy
    exact hf.1 (hg.1 hxy)
  · intro A x hA hx
    have hgSup : IsSup (g '' A) (g x) := hg.2 hA hx
    have hdirg : DirectedSet (g '' A) := DirectedSet.image hg.1 hA
    have hfSup : IsSup (f '' (g '' A)) (f (g x)) := hf.2 hdirg hgSup
    have himage : (fun x : α => f (g x)) '' A = f '' (g '' A) := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨a, ha, rfl⟩
        exact ⟨g a, ⟨a, ha, rfl⟩, rfl⟩
      · intro hz
        rcases hz with ⟨b, hb, rfl⟩
        rcases hb with ⟨a, ha, rfl⟩
        exact ⟨a, ha, rfl⟩
    simpa [himage] using hfSup

end MonotoneAndDirected

section Fixpoints

variable {α : Type u} [PartialOrder α] [OrderBot α]

/-- Iterates from bottom, used in Theorem 2.1.19. -/
def botIter (f : α → α) : Nat → α
  | 0 => ⊥
  | n + 1 => f (botIter f n)

/-- The Kleene chain/set `{fⁿ(⊥) | n ∈ ℕ}`. -/
def iterSet (f : α → α) : Set α :=
  Set.range (botIter f)

lemma botIter_le_succ {f : α → α} (hf : Monotone f) :
    ∀ n : Nat, botIter f n ≤ botIter f (n + 1) := by
  intro n
  induction n with
  | zero =>
      exact bot_le
  | succ n ih =>
      exact hf ih

lemma botIter_mono {f : α → α} (hf : Monotone f) :
    Monotone (botIter f) := by
  intro m n hmn
  induction hmn with
  | refl =>
      exact le_rfl
  | step hmn ih =>
      exact le_trans ih (botIter_le_succ hf _)

lemma iterSet_directed {f : α → α} (hf : Monotone f) :
    DirectedSet (iterSet f) := by
  constructor
  · exact ⟨⊥, ⟨0, rfl⟩⟩
  · intro x hx y hy
    rcases hx with ⟨m, rfl⟩
    rcases hy with ⟨n, rfl⟩
    refine ⟨botIter f (max m n), ⟨max m n, rfl⟩, ?_, ?_⟩
    · exact botIter_mono hf (Nat.le_max_left m n)
    · exact botIter_mono hf (Nat.le_max_right m n)

/-- Least fixed point predicate. -/
def IsLeastFixedPoint (f : α → α) (x : α) : Prop :=
  f x = x ∧ ∀ y : α, f y = y → x ≤ y

/-- Theorem 2.1.19(1), predicate version: if the Kleene chain has a supremum and
    `f` preserves that supremum, then this supremum is the least fixed point. -/
theorem theorem_2_1_19_1
    {f : α → α} (hf : ScottContinuous f) {l : α}
    (hl : IsSup (iterSet f) l) : IsLeastFixedPoint f l := by
  have hdir : DirectedSet (iterSet f) := iterSet_directed hf.1
  have hsupImage : IsSup (f '' iterSet f) (f l) := hf.2 hdir hl
  have hsupImage_l : IsSup (f '' iterSet f) l := by
    constructor
    · intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      rcases hz with ⟨n, rfl⟩
      exact hl.1 ⟨n + 1, rfl⟩
    · intro y hy
      exact hl.2 y (by
        intro z hz
        rcases hz with ⟨n, rfl⟩
        cases n with
        | zero => exact bot_le
        | succ n =>
            exact hy ⟨botIter f n, ⟨n, rfl⟩, rfl⟩)
  constructor
  · exact IsSup.unique hsupImage hsupImage_l
  · intro y hy
    exact hl.2 y (by
      intro z hz
      rcases hz with ⟨n, rfl⟩
      induction n with
      | zero => exact bot_le
      | succ n ih =>
          calc
            botIter f (n + 1) = f (botIter f n) := rfl
            _ ≤ f y := hf.1 ih
            _ = y := hy)

/-- Admissible predicates used in Lemma 2.1.20, using ω-chain/range suprema. -/
def OmegaAdmissible (P : Set α) : Prop :=
  ⊥ ∈ P ∧ ∀ ⦃c : Nat → α⦄ ⦃l : α⦄,
    Monotone c → IsSup (Set.range c) l → (∀ n : Nat, c n ∈ P) → l ∈ P

/-- Lemma 2.1.20: fixed-point induction, predicate version. -/
theorem lemma_2_1_20 {P : Set α} {f : α → α} {l : α}
    (hf : Monotone f) (hP : OmegaAdmissible P)
    (hstep : ∀ x ∈ P, f x ∈ P)
    (hl : IsSup (iterSet f) l) : l ∈ P := by
  refine hP.2 (botIter_mono hf) (by simpa [iterSet] using hl) ?_
  intro n
  induction n with
  | zero => exact hP.1
  | succ n ih => exact hstep (botIter f n) ih

end Fixpoints
end Chapter2
end AbramskyJung

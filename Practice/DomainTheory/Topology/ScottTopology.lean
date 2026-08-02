import Practice.DomainTheory.Order.WayBelow

/-!
# Chapter 2 Scott topology

Scott-open and Scott-closed predicates, with the basic neighborhood lemmas used
by the numbered Chapter 2 coverage.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u v w

namespace AbramskyJung
namespace Chapter2

section ScottTopology

variable {α : Type u} [Preorder α]

/-- Definition 2.3.1, preorder/existing-supremum form: Scott-closed sets are
lower sets closed under every directed supremum that exists in the ambient
preorder. -/
def ScottClosed (C : Set α) : Prop :=
  IsLowerSet C ∧ ∀ ⦃A : Set α⦄ ⦃s : α⦄,
    DirectedSet A → A ⊆ C → IsSup A s → s ∈ C

/-- Definition 2.3.1: Scott-open sets, as complements of Scott-closed sets. -/
def ScottOpen (O : Set α) : Prop :=
  ScottClosed Oᶜ

/-- Definition 2.3.1: the Scott topology as the unbundled set of Scott-open
subsets.  The lightweight topology laws are proved below rather than packaged
as a mathlib `TopologicalSpace`. -/
def ScottTopology (α : Type u) [Preorder α] : Set (Set α) :=
  {O | ScottOpen O}

/-- Scott-open sets are upper sets. -/
theorem scottOpen_upper {O : Set α} (hO : ScottOpen O) : IsUpperSet O := by
  intro x y hx hxy
  by_contra hy
  have hxnot : x ∉ O := hO.1 hy hxy
  exact hxnot hx

/-- Definition 2.3.1 topology law: the empty set is Scott-open. -/
theorem scottOpen_empty : ScottOpen (∅ : Set α) := by
  constructor
  · intro _ _ _ _
    simp
  · intro _ _ _ _ _
    simp

/-- Definition 2.3.1 topology law: the full carrier is Scott-open. -/
theorem scottOpen_univ : ScottOpen (Set.univ : Set α) := by
  constructor
  · intro _ _ hy _
    simpa using hy
  · intro A _ hA hAs _
    rcases hA.1 with ⟨a, ha⟩
    have hfalse : False := by
      simpa using hAs ha
    exact False.elim hfalse

/-- Definition 2.3.1 topology law: binary intersections of Scott-open sets are
Scott-open. -/
theorem scottOpen_inter {U V : Set α} (hU : ScottOpen U) (hV : ScottOpen V) :
    ScottOpen (U ∩ V) := by
  classical
  constructor
  · intro x y hy hxy hxUV
    exact hy ⟨scottOpen_upper hU hxUV.1 hxy, scottOpen_upper hV hxUV.2 hxy⟩
  · intro A s hA hAs hs hsUV
    have hnotU : ¬ A ⊆ Uᶜ := by
      intro hAU
      exact (hU.2 hA hAU hs) hsUV.1
    have hnotV : ¬ A ⊆ Vᶜ := by
      intro hAV
      exact (hV.2 hA hAV hs) hsUV.2
    obtain ⟨a, haA, haU⟩ : ∃ a ∈ A, a ∈ U := by
      by_contra hnone
      exact hnotU (by
        intro a haA haU
        exact hnone ⟨a, haA, haU⟩)
    obtain ⟨b, hbA, hbV⟩ : ∃ b ∈ A, b ∈ V := by
      by_contra hnone
      exact hnotV (by
        intro b hbA hbV
        exact hnone ⟨b, hbA, hbV⟩)
    rcases hA.2 haA hbA with ⟨c, hcA, hac, hbc⟩
    exact hAs hcA ⟨scottOpen_upper hU haU hac, scottOpen_upper hV hbV hbc⟩

/-- Principal ideals are Scott-closed. -/
theorem scottClosed_principal_ideal (x : α) :
    ScottClosed (lowerClosure ({x} : Set α)) := by
  constructor
  · intro a b hb hab
    rcases hb with ⟨z, hz, hbz⟩
    exact ⟨z, hz, le_trans hab hbz⟩
  · intro A s hdir hA hs
    exact ⟨x, by simp, hs.2 x (by
      intro a ha
      rcases hA ha with ⟨z, hz, haz⟩
      have hzx : z = x := by simpa using hz
      simpa [hzx] using haz)⟩

/-- Definition 2.3.1: Scott closure, defined as membership in every Scott-closed
superset. -/
def ScottClosureMem (A : Set α) (x : α) : Prop :=
  ∀ C : Set α, ScottClosed C → A ⊆ C → x ∈ C

/-- Proposition 2.3.2(1), `(a) -> (b)`: the specialization preorder of the Scott
    topology extends the order. -/
theorem prop_2_3_2_order_to_open {x y : α} (hxy : x ≤ y) :
    ∀ O : Set α, ScottOpen O → x ∈ O → y ∈ O := by
  intro O hO hxO
  exact scottOpen_upper hO hxO hxy

/-- Proposition 2.3.2(1), `(b) -> (a)`: Scott opens reconstruct the order. -/
theorem prop_2_3_2_open_to_order {x y : α}
    (h : ∀ O : Set α, ScottOpen O → x ∈ O → y ∈ O) : x ≤ y := by
  classical
  by_contra hxy
  let C : Set α := lowerClosure ({y} : Set α)
  have hC : ScottClosed C := scottClosed_principal_ideal y
  have hxO : x ∈ Cᶜ := by
    intro hxC
    rcases hxC with ⟨z, hz, hxz⟩
    have hzy : z = y := by simpa using hz
    exact hxy (by simpa [hzy] using hxz)
  have hOpenCcompl : ScottOpen Cᶜ := by
    simpa [ScottOpen] using hC
  have hyO : y ∈ Cᶜ := h Cᶜ hOpenCcompl hxO
  exact hyO ⟨y, by simp, le_rfl⟩

/-- Proposition 2.3.2(1): order is exactly the Scott specialization preorder. -/
theorem prop_2_3_2_order_open_iff {x y : α} :
    x ≤ y ↔ ∀ O : Set α, ScottOpen O → x ∈ O → y ∈ O := by
  constructor
  · exact prop_2_3_2_order_to_open
  · exact prop_2_3_2_open_to_order

/-- Proposition 2.3.2(1), `(a) -> (c)`: order implies Scott-closure membership of
    the singleton. -/
theorem prop_2_3_2_order_to_closure {x y : α} (hxy : x ≤ y) :
    ScottClosureMem ({y} : Set α) x := by
  intro C hC hyC
  exact hC.1 (hyC (by simp)) hxy

/-- Proposition 2.3.2(1), `(c) -> (a)`. -/
theorem prop_2_3_2_closure_to_order {x y : α}
    (h : ScottClosureMem ({y} : Set α) x) : x ≤ y := by
  have hx : x ∈ lowerClosure ({y} : Set α) :=
    h (lowerClosure ({y} : Set α)) (scottClosed_principal_ideal y) (by
      intro z hz
      have hzy : z = y := by simpa using hz
      exact ⟨y, by simp, by simpa [hzy]⟩)
  rcases hx with ⟨z, hz, hxz⟩
  have hzy : z = y := by simpa using hz
  simpa [hzy] using hxz

/-- Proposition 2.3.2(1): closure of singletons also reconstructs the order. -/
theorem prop_2_3_2_order_closure_iff {x y : α} :
    x ≤ y ↔ ScottClosureMem ({y} : Set α) x := by
  constructor
  · exact prop_2_3_2_order_to_closure
  · exact prop_2_3_2_closure_to_order

/-- Topological Scott-continuity: inverse images of Scott-open sets are Scott-open. -/
def TopologicallyScottContinuous {β : Type v} [Preorder β] (f : α → β) : Prop :=
  ∀ O : Set β, ScottOpen O → ScottOpen (f ⁻¹' O)

/-- Proposition 2.3.4, easy direction: order-theoretic Scott-continuity implies
    topological continuity for Scott topologies. -/
theorem prop_2_3_4_forward {β : Type v} [Preorder β] {f : α → β}
    (hf : ScottContinuous f) : TopologicallyScottContinuous f := by
  intro O hO
  constructor
  · intro x y hy hxy
    exact hO.1 hy (hf.1 hxy)
  · intro A s hdir hA hs
    have hsImg : IsSup (f '' A) (f s) := hf.2 hdir hs
    exact hO.2 (DirectedSet.image hf.1 hdir) (by
      intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact hA ha) hsImg

/-- Proposition 2.3.5, expressed with `↑↑x`: membership in `↑↑x` is by definition
    the same as `x ≪ y`. -/
theorem prop_2_3_5_wayBelowUpper {x y : α} :
    x ≪ y ↔ y ∈ wayBelowUpper x := by
  rfl

/-- Proposition 2.3.6, first direction in predicate form: every Scott-open set is the
    union of its way-below neighborhoods in a continuous domain. -/
theorem prop_2_3_6_open_supported_by_wayBelow
    (hcont : IsContinuousDomain α) {O : Set α} (hO : ScottOpen O) :
    O = ⋃ x ∈ O, wayBelowUpper x := by
  ext y
  constructor
  · intro hy
    rcases hcont with ⟨B, hBraw⟩
    have hB : IsBasis B := prop_2_2_4_1 hBraw
    have hdir : DirectedSet (Approximants B y) := (hB y).1
    have hsup : IsSup (Approximants B y) y := (hB y).2
    by_contra hnot
    have hcomp : Approximants B y ⊆ Oᶜ := by
      intro b hb hbO
      have hyInUnion : y ∈ ⋃ x ∈ O, wayBelowUpper x := by
        rw [Set.mem_iUnion]
        refine ⟨b, ?_⟩
        rw [Set.mem_iUnion]
        exact ⟨hbO, hb.2⟩
      exact hnot hyInUnion
    have hyComp : y ∈ Oᶜ := hO.2 hdir hcomp hsup
    exact hyComp hy
  · intro hy
    rw [Set.mem_iUnion] at hy
    rcases hy with ⟨x, hxrest⟩
    rw [Set.mem_iUnion] at hxrest
    rcases hxrest with ⟨hxO, hxy⟩
    exact scottOpen_upper hO hxO (prop_2_2_2_1 hxy)

end ScottTopology
end Chapter2
end AbramskyJung

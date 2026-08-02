import Practice.DomainTheory.Chapter02

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Chapter 3 prelude

Shared imports and reducible aliases for the split Chapter 3 files.

Chapter 3 intentionally reuses Chapter 2's order-theoretic definitions instead
of redefining directed sets, suprema, Scott-continuity, way-below, and bases.
The aliases below preserve the Chapter 3 namespace used by the original
single-file draft while keeping the implementation tied to Chapter 2.
-/

universe u v w z

namespace AbramskyJung
namespace Chapter3

abbrev IsUpperBound {α : Type u} [Preorder α] : Set α → α → Prop :=
  Chapter2.IsUpperBound

abbrev IsLowerBound {α : Type u} [Preorder α] : Set α → α → Prop :=
  Chapter2.IsLowerBound

abbrev IsSup {α : Type u} [Preorder α] : Set α → α → Prop :=
  Chapter2.IsSup

abbrev IsInf {α : Type u} [Preorder α] : Set α → α → Prop :=
  Chapter2.IsInf

abbrev DirectedSet {α : Type u} [Preorder α] : Set α → Prop :=
  Chapter2.DirectedSet

abbrev IsDcpo (α : Type u) [Preorder α] : Prop :=
  Chapter2.IsDcpo α

abbrev ScottContinuous {α : Type u} {β : Type v} [Preorder α] [Preorder β]
    (f : α → β) : Prop :=
  Chapter2.ScottContinuous f

abbrev WayBelow {α : Type u} [Preorder α] (x y : α) : Prop :=
  Chapter2.WayBelow x y

abbrev Compact {α : Type u} [Preorder α] (x : α) : Prop :=
  Chapter2.Compact x

abbrev Approximants {α : Type u} [Preorder α] (B : Set α) (x : α) : Set α :=
  Chapter2.Approximants B x

abbrev IsBasis {α : Type u} [Preorder α] (B : Set α) : Prop :=
  Chapter2.IsBasis B

/-- Chapter 3 works with the strong basis predicate from Chapter 2. -/
abbrev IsContinuousDomain (α : Type u) [Preorder α] : Prop :=
  ∃ B : Set α, IsBasis B

/-- Algebraicity in the Chapter 3 strong-basis presentation. -/
abbrev IsAlgebraicDomain (α : Type u) [Preorder α] : Prop :=
  IsBasis ({x : α | Compact x} : Set α)

theorem IsSup.unique {α : Type u} [PartialOrder α] {A : Set α} {x y : α}
    (hx : IsSup A x) (hy : IsSup A y) : x = y :=
  Chapter2.IsSup.unique hx hy

theorem IsInf.unique {α : Type u} [PartialOrder α] {A : Set α} {x y : α}
    (hx : IsInf A x) (hy : IsInf A y) : x = y :=
  Chapter2.IsInf.unique hx hy

theorem DirectedSet.image {α : Type u} {β : Type v} [Preorder α] [Preorder β]
    {A : Set α} {f : α → β} (hf : Monotone f) (hA : DirectedSet A) :
    DirectedSet (f '' A) :=
  Chapter2.DirectedSet.image hf hA

theorem ScottContinuous.monotone {α : Type u} {β : Type v} [Preorder α] [Preorder β]
    {f : α → β} (hf : ScottContinuous f) : Monotone f :=
  Chapter2.ScottContinuous.monotone hf

theorem scottContinuous_id {α : Type u} [Preorder α] :
    ScottContinuous (fun x : α => x) :=
  Chapter2.scottContinuous_id

theorem ScottContinuous.comp {α : Type u} {β : Type v} {γ : Type w}
    [Preorder α] [Preorder β] [Preorder γ] {f : β → γ} {g : α → β}
    (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous (fun x : α => f (g x)) :=
  Chapter2.ScottContinuous.comp hf hg

theorem wayBelow_le {α : Type u} [Preorder α] {x y : α}
    (h : WayBelow x y) : x ≤ y :=
  Chapter2.prop_2_2_2_1 h

theorem wayBelow_mono {α : Type u} [Preorder α] {x x' y y' : α}
    (hx : x' ≤ x) (hxy : WayBelow x y) (hy : y ≤ y') : WayBelow x' y' :=
  Chapter2.prop_2_2_2_2 hx hxy hy

end Chapter3
end AbramskyJung

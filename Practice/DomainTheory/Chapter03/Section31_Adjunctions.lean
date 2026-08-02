import Practice.DomainTheory.Chapter03.Prelude

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 3.1: adjunctions

This file records the adjunction material from Section 3.1 and reuses the
order-theoretic notions imported through the Chapter 3 prelude.
-/

universe u v

namespace AbramskyJung
namespace Chapter3

section Adjunctions

variable {P : Type u} [Preorder P]
variable {Q : Type v} [Preorder Q]

/-- Definition 3.1.11: adjunctions between posets. -/
structure Adjunction (l : P → Q) (u : Q → P) : Prop where
  adj : ∀ x : P, ∀ y : Q, x ≤ u y ↔ l x ≤ y

namespace Adjunction

variable {l : P → Q} {r : Q → P}

/-- The lower adjoint is monotone. -/
theorem monotone_l (h : Adjunction l r) : Monotone l := by
  intro x x' hxx'
  have hx' : x' ≤ r (l x') := (h.adj x' (l x')).2 le_rfl
  exact (h.adj x (l x')).1 (le_trans hxx' hx')

/-- The upper adjoint is monotone. -/
theorem monotone_u (h : Adjunction l r) : Monotone r := by
  intro y y' hyy'
  have hy : l (r y) ≤ y := (h.adj (r y) y).1 le_rfl
  exact (h.adj (r y) y').2 (le_trans hy hyy')

/-- Unit inequality: `id ≤ u ∘ l`. -/
theorem unit (h : Adjunction l r) (x : P) : x ≤ r (l x) :=
  (h.adj x (l x)).2 le_rfl

/-- Counit inequality: `l ∘ u ≤ id`. -/
theorem counit (h : Adjunction l r) (y : Q) : l (r y) ≤ y :=
  (h.adj (r y) y).1 le_rfl

end Adjunction

/-- Proposition 3.1.10, formulation via unit/counit inequalities. -/
theorem adjunction_of_unit_counit {l : P → Q} {u : Q → P}
    (hl : Monotone l) (hu : Monotone u)
    (hunit : ∀ x : P, x ≤ u (l x))
    (hcounit : ∀ y : Q, l (u y) ≤ y) :
    Adjunction l u := by
  constructor
  intro x y
  constructor
  · intro hxy
    exact le_trans (hl hxy) (hcounit y)
  · intro hxy
    exact le_trans (hunit x) (hu hxy)

/-- Proposition 3.1.12(5): lower adjoints preserve existing suprema. -/
theorem lower_adjoint_preserves_sup {l : P → Q} {u : Q → P}
    (h : Adjunction l u) {A : Set P} {s : P} (hs : IsSup A s) :
    IsSup (l '' A) (l s) := by
  constructor
  · intro z hz
    rcases hz with ⟨a, ha, rfl⟩
    exact Adjunction.monotone_l h (hs.1 ha)
  · intro y hy
    exact (h.adj s y).1 (hs.2 (u y) (by
      intro a ha
      exact (h.adj a y).2 (hy ⟨a, ha, rfl⟩)))

/-- Proposition 3.1.12(5): upper adjoints preserve existing infima. -/
theorem upper_adjoint_preserves_inf {l : P → Q} {u : Q → P}
    (h : Adjunction l u) {A : Set Q} {s : Q} (hs : IsInf A s) :
    IsInf (u '' A) (u s) := by
  constructor
  · intro z hz
    rcases hz with ⟨a, ha, rfl⟩
    exact Adjunction.monotone_u h (hs.1 ha)
  · intro y hy
    exact (h.adj y s).2 (hs.2 (l y) (by
      intro a ha
      exact (h.adj y a).1 (hy ⟨a, ha, rfl⟩)))

/-- Proposition 3.1.12(1): `u ∘ l ∘ u = u`, with explicit antisymmetry for the
current preorder-based interface. -/
theorem upper_lower_upper_eq {l : P → Q} {u : Q → P}
    (h : Adjunction l u) (hPanti : ∀ x y : P, x ≤ y → y ≤ x → x = y)
    (y : Q) : u (l (u y)) = u y := by
  apply hPanti
  · exact Adjunction.monotone_u h (Adjunction.counit h y)
  · exact Adjunction.unit h (u y)

/-- Proposition 3.1.12(1): `l ∘ u ∘ l = l`, with explicit antisymmetry for the
current preorder-based interface. -/
theorem lower_upper_lower_eq {l : P → Q} {u : Q → P}
    (h : Adjunction l u) (hQanti : ∀ x y : Q, x ≤ y → y ≤ x → x = y)
    (x : P) : l (u (l x)) = l x := by
  apply hQanti
  · exact Adjunction.counit h (l x)
  · exact Adjunction.monotone_l h (Adjunction.unit h x)

/-- Proposition 3.1.12(1), packaged composition equations. -/
structure AdjunctionCompositionLaws
    {l : P → Q} {u : Q → P} (h : Adjunction l u) : Prop where
  upper_lower_upper : ∀ y : Q, u (l (u y)) = u y
  lower_upper_lower : ∀ x : P, l (u (l x)) = l x

/-- Proposition 3.1.12(1): the two idempotence equations of an adjunction. -/
theorem adjunction_composition_laws {l : P → Q} {u : Q → P}
    (h : Adjunction l u)
    (hPanti : ∀ x y : P, x ≤ y → y ≤ x → x = y)
    (hQanti : ∀ x y : Q, x ≤ y → y ≤ x → x = y) :
    AdjunctionCompositionLaws h where
  upper_lower_upper := upper_lower_upper_eq h hPanti
  lower_upper_lower := lower_upper_lower_eq h hQanti

/-- Proposition 3.1.12(2): the images of the upper and lower adjoints are
order-isomorphic via the restrictions of `l` and `u`. -/
structure AdjunctionImageOrderIso
    {l : P → Q} {u : Q → P} (h : Adjunction l u) where
  toLowerImage : {p : P // p ∈ Set.range u} → {q : Q // q ∈ Set.range l}
  toUpperImage : {q : Q // q ∈ Set.range l} → {p : P // p ∈ Set.range u}
  left_inverse : ∀ x, toUpperImage (toLowerImage x) = x
  right_inverse : ∀ y, toLowerImage (toUpperImage y) = y
  toLower_mono : ∀ {x y}, x ≤ y → toLowerImage x ≤ toLowerImage y
  toUpper_mono : ∀ {x y}, x ≤ y → toUpperImage x ≤ toUpperImage y

/-- Proposition 3.1.12(2), constructed from the restrictions of `l` and `u` to
their images. -/
def adjunction_image_order_iso {l : P → Q} {u : Q → P}
    (h : Adjunction l u)
    (hPanti : ∀ x y : P, x ≤ y → y ≤ x → x = y)
    (hQanti : ∀ x y : Q, x ≤ y → y ≤ x → x = y) :
    AdjunctionImageOrderIso h where
  toLowerImage := fun x => ⟨l x.1, ⟨x.1, rfl⟩⟩
  toUpperImage := fun y => ⟨u y.1, ⟨y.1, rfl⟩⟩
  left_inverse := by
    intro x
    rcases x with ⟨px, hpx⟩
    rcases hpx with ⟨q, rfl⟩
    apply Subtype.ext
    exact upper_lower_upper_eq h hPanti q
  right_inverse := by
    intro y
    rcases y with ⟨qy, hqy⟩
    rcases hqy with ⟨p, rfl⟩
    apply Subtype.ext
    exact lower_upper_lower_eq h hQanti p
  toLower_mono := by
    intro x y hxy
    exact Adjunction.monotone_l h hxy
  toUpper_mono := by
    intro x y hxy
    exact Adjunction.monotone_u h hxy

/-- Proposition 3.1.12(3): surjectivity of the upper adjoint, the unit equation,
and injectivity of the lower adjoint are equivalent. -/
structure UpperSurjectiveUnitLowerInjective
    {l : P → Q} {u : Q → P} (h : Adjunction l u) : Prop where
  upper_surjective_iff_unit_eq :
    Function.Surjective u ↔ ∀ x : P, u (l x) = x
  unit_eq_iff_lower_injective :
    (∀ x : P, u (l x) = x) ↔ Function.Injective l

/-- Proposition 3.1.12(3), proved from the composition laws. -/
theorem upper_surjective_unit_lower_injective {l : P → Q} {u : Q → P}
    (h : Adjunction l u)
    (hPanti : ∀ x y : P, x ≤ y → y ≤ x → x = y)
    (hQanti : ∀ x y : Q, x ≤ y → y ≤ x → x = y) :
    UpperSurjectiveUnitLowerInjective h where
  upper_surjective_iff_unit_eq := by
    constructor
    · intro hsurj x
      rcases hsurj x with ⟨y, rfl⟩
      exact upper_lower_upper_eq h hPanti y
    · intro hunit x
      exact ⟨l x, hunit x⟩
  unit_eq_iff_lower_injective := by
    constructor
    · intro hunit x y hxy
      calc
        x = u (l x) := (hunit x).symm
        _ = u (l y) := by rw [hxy]
        _ = y := hunit y
    · intro hinj x
      exact hinj (lower_upper_lower_eq h hQanti x)

/-- Proposition 3.1.12(4): surjectivity of the lower adjoint, the counit
equation, and injectivity of the upper adjoint are equivalent. -/
structure LowerSurjectiveCounitUpperInjective
    {l : P → Q} {u : Q → P} (h : Adjunction l u) : Prop where
  lower_surjective_iff_counit_eq :
    Function.Surjective l ↔ ∀ y : Q, l (u y) = y
  counit_eq_iff_upper_injective :
    (∀ y : Q, l (u y) = y) ↔ Function.Injective u

/-- Proposition 3.1.12(4), proved from the composition laws. -/
theorem lower_surjective_counit_upper_injective {l : P → Q} {u : Q → P}
    (h : Adjunction l u)
    (hPanti : ∀ x y : P, x ≤ y → y ≤ x → x = y)
    (hQanti : ∀ x y : Q, x ≤ y → y ≤ x → x = y) :
    LowerSurjectiveCounitUpperInjective h where
  lower_surjective_iff_counit_eq := by
    constructor
    · intro hsurj y
      rcases hsurj y with ⟨x, rfl⟩
      exact lower_upper_lower_eq h hQanti x
    · intro hcounit y
      exact ⟨u y, hcounit y⟩
  counit_eq_iff_upper_injective := by
    constructor
    · intro hcounit x y hxy
      calc
        x = l (u x) := (hcounit x).symm
        _ = l (u y) := by rw [hxy]
        _ = y := hcounit y
    · intro hinj y
      exact hinj (upper_lower_upper_eq h hPanti y)

/-- One direction of Proposition 3.1.13: having a lower adjoint implies preservation of infima. -/
theorem has_lower_adjoint_preserves_inf {f : Q → P} {g : P → Q}
    (h : Adjunction g f) {A : Set Q} {s : Q} (hs : IsInf A s) :
    IsInf (f '' A) (f s) :=
  upper_adjoint_preserves_inf h hs

/-- One direction of Proposition 3.1.13: having an upper adjoint implies preservation of suprema. -/
theorem has_upper_adjoint_preserves_sup {f : P → Q} {g : Q → P}
    (h : Adjunction f g) {A : Set P} {s : P} (hs : IsSup A s) :
    IsSup (f '' A) (f s) :=
  lower_adjoint_preserves_sup h hs

/-- A monotone map preserves all existing suprema. -/
def PreservesAllSuprema
    {L : Type u} {P : Type v} [Preorder L] [Preorder P] (f : L → P) : Prop :=
  ∀ A : Set L, ∀ s : L, IsSup A s → IsSup (f '' A) (f s)

/-- A map has an upper adjoint. -/
def HasUpperAdjoint
    {L : Type u} {P : Type v} [Preorder L] [Preorder P] (f : L → P) : Prop :=
  ∃ g : P → L, Adjunction f g

/-- Proposition 3.1.14(1): a lower adjoint is Scott-continuous. -/
theorem lower_adjoint_scottContinuous {l : P → Q} {u : Q → P}
    (h : Adjunction l u) : ScottContinuous l := by
  constructor
  · exact Adjunction.monotone_l h
  · intro A x hA hx
    exact lower_adjoint_preserves_sup h hx

/-- Proposition 3.1.14(2): if the upper adjoint is Scott-continuous, the lower adjoint
preserves the way-below relation. -/
theorem lower_adjoint_preserves_wayBelow {l : P → Q} {u : Q → P}
    (h : Adjunction l u) (hu : ScottContinuous u) {x y : P}
    (hxy : WayBelow x y) : WayBelow (l x) (l y) := by
  intro A s hA hs hlys
  have huSup : IsSup (u '' A) (u s) := hu.2 hA hs
  have huDir : DirectedSet (u '' A) := DirectedSet.image hu.1 hA
  have hyus : y ≤ u s := (h.adj y s).2 hlys
  rcases hxy huDir huSup hyus with ⟨uy, huy, hxuy⟩
  rcases huy with ⟨a, ha, rfl⟩
  exact ⟨a, ha, (h.adj x a).1 hxuy⟩

/-- Proposition 3.1.14(3), predicate version: on a continuous domain, if the lower
adjoint preserves way-below, then the upper adjoint is Scott-continuous. -/
theorem upper_adjoint_scottContinuous_of_preserves_wayBelow
    {l : P → Q} {u : Q → P} (h : Adjunction l u)
    (hcont : IsContinuousDomain P)
    (hpres : ∀ ⦃x y : P⦄, WayBelow x y → WayBelow (l x) (l y)) :
    ScottContinuous u := by
  constructor
  · exact Adjunction.monotone_u h
  · intro A s hA hs
    constructor
    · intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact Adjunction.monotone_u h (hs.1 ha)
    · intro z hz
      rcases hcont with ⟨B, hB⟩
      have hApproxLeZ : IsUpperBound (Approximants B (u s)) z := by
        intro b hb
        have hlb : WayBelow (l b) (l (u s)) := hpres hb.2
        have hlb_s : WayBelow (l b) s := wayBelow_mono le_rfl hlb (Adjunction.counit h s)
        rcases hlb_s hA hs le_rfl with ⟨a, ha, hlba⟩
        have hbu : b ≤ u a := (h.adj b a).2 hlba
        exact le_trans hbu (hz ⟨a, ha, rfl⟩)
      exact (hB (u s)).2.2 z hApproxLeZ

end Adjunctions

end Chapter3
end AbramskyJung

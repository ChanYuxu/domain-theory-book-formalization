import Practice.DomainTheory.Chapter04.Section43_FunctionSpaceSupport

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Figure 11 function-space infrastructure

Finite-diagram order facts, the four-region maps, and the open-step
approximations needed by the corrected Figure 11 obstruction.
-/

universe u

namespace AbramskyJung
namespace Chapter4

namespace Figure11XDiagram

/-- The displayed bottom point supplies the bottom structure used by open-step
functions into Figure 11's domain `X`. -/
@[reducible] def orderBot {X : OrderedDomain.{u}} (hX : Figure11XDiagram X) :
    OrderBot X.carrier where
  bot := hX.point 0
  bot_le x := by
    rcases hX.point_bijective.2 x with ⟨i, rfl⟩
    exact (hX.order_iff 0 i).2 (by simp [Figure11XLe])

/-- Every point of the finite Figure 11 domain is compact. -/
theorem point_compact {X : OrderedDomain.{u}} (hX : Figure11XDiagram X)
    (i : Fin 6) : Chapter3.Compact (hX.point i) := by
  letI : Finite X.carrier :=
    Finite.of_surjective hX.point hX.point_bijective.2
  intro A s hA hs his
  rcases hA.exists_isSup_of_finite (Set.toFinite A) with ⟨a, ha, haSup⟩
  exact ⟨a, ha, le_trans his (hs.2 a haSup.1)⟩

theorem bottom_le {X : OrderedDomain.{u}} (hX : Figure11XDiagram X)
    (x : X.carrier) : hX.point 0 ≤ x :=
  (hX.orderBot).bot_le x

theorem left_le_joint {X : OrderedDomain.{u}} (hX : Figure11XDiagram X)
    {j : Fin 6} (hj : j = 3 ∨ j = 4 ∨ j = 5) :
    hX.point 1 ≤ hX.point j := by
  apply (hX.order_iff 1 j).2
  rcases hj with rfl | rfl | rfl <;> simp [Figure11XLe]

theorem right_le_joint {X : OrderedDomain.{u}} (hX : Figure11XDiagram X)
    {j : Fin 6} (hj : j = 3 ∨ j = 4 ∨ j = 5) :
    hX.point 2 ≤ hX.point j := by
  apply (hX.order_iff 2 j).2
  rcases hj with rfl | rfl | rfl <;> simp [Figure11XLe]

end Figure11XDiagram

/-- The four-region map determined by two Scott opens.  Joint index `3` is the
book's `c₁`; joint index `5` is `⊤`. -/
noncomputable def Figure11PairFunction
    {D : Type u} [Preorder D] {X : OrderedDomain.{u}}
    (hX : Figure11XDiagram X) (joint : Fin 6)
    (U₁ U₂ : ScottOpenCarrier
      ({ carrier := D, preorder := inferInstance } : OrderedDomain)) :
    D → X.carrier := by
  classical
  exact fun x =>
    if x ∈ U₁.carrierSet then
      if x ∈ U₂.carrierSet then hX.point joint else hX.point 1
    else if x ∈ U₂.carrierSet then hX.point 2 else hX.point 0

theorem figure11PairFunction_monotone
    {D : Type u} [Preorder D] {X : OrderedDomain.{u}}
    (hX : Figure11XDiagram X) {joint : Fin 6}
    (hjoint : joint = 3 ∨ joint = 4 ∨ joint = 5)
    (U₁ U₂ : ScottOpenCarrier
      ({ carrier := D, preorder := inferInstance } : OrderedDomain)) :
    Monotone (Figure11PairFunction hX joint U₁ U₂) := by
  classical
  intro x y hxy
  by_cases hx₁ : x ∈ U₁.carrierSet
  · have hy₁ : y ∈ U₁.carrierSet :=
      Chapter2.scottOpen_upper U₁.scott_open hx₁ hxy
    by_cases hx₂ : x ∈ U₂.carrierSet
    · have hy₂ : y ∈ U₂.carrierSet :=
        Chapter2.scottOpen_upper U₂.scott_open hx₂ hxy
      simp [Figure11PairFunction, hx₁, hx₂, hy₁, hy₂]
    · by_cases hy₂ : y ∈ U₂.carrierSet
      · simpa [Figure11PairFunction, hx₁, hx₂, hy₁, hy₂] using
          hX.left_le_joint hjoint
      · simp [Figure11PairFunction, hx₁, hx₂, hy₁, hy₂]
  · by_cases hx₂ : x ∈ U₂.carrierSet
    · have hy₂ : y ∈ U₂.carrierSet :=
        Chapter2.scottOpen_upper U₂.scott_open hx₂ hxy
      by_cases hy₁ : y ∈ U₁.carrierSet
      · simpa [Figure11PairFunction, hx₁, hx₂, hy₁, hy₂] using
          hX.right_le_joint hjoint
      · simp [Figure11PairFunction, hx₁, hx₂, hy₁, hy₂]
    · simpa [Figure11PairFunction, hx₁, hx₂] using
        hX.bottom_le (Figure11PairFunction hX joint U₁ U₂ y)

theorem exists_mem_of_sup_mem_scottOpen
    {D : Type u} [Preorder D] {A : Set D} {s : D}
    (hA : Chapter3.DirectedSet A) (hs : Chapter3.IsSup A s)
    (U : ScottOpenCarrier
      ({ carrier := D, preorder := inferInstance } : OrderedDomain))
    (hsU : s ∈ U.carrierSet) :
    ∃ x ∈ A, x ∈ U.carrierSet := by
  by_contra hnone
  have hAcompl : A ⊆ U.carrierSetᶜ := by
    intro x hxA hxU
    exact hnone ⟨x, hxA, hxU⟩
  exact (U.scott_open.2 hA hAcompl hs) hsU

theorem figure11PairFunction_scottContinuous
    {D : Type u} [Preorder D] {X : OrderedDomain.{u}}
    (hX : Figure11XDiagram X) {joint : Fin 6}
    (hjoint : joint = 3 ∨ joint = 4 ∨ joint = 5)
    (U₁ U₂ : ScottOpenCarrier
      ({ carrier := D, preorder := inferInstance } : OrderedDomain)) :
    Chapter3.ScottContinuous (Figure11PairFunction hX joint U₁ U₂) := by
  classical
  constructor
  · exact figure11PairFunction_monotone hX hjoint U₁ U₂
  · intro A s hA hs
    constructor
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact figure11PairFunction_monotone hX hjoint U₁ U₂ (hs.1 hx)
    · intro y hy
      by_cases hs₁ : s ∈ U₁.carrierSet
      · by_cases hs₂ : s ∈ U₂.carrierSet
        · rcases exists_mem_of_sup_mem_scottOpen hA hs U₁ hs₁ with
            ⟨x₁, hx₁A, hx₁U⟩
          rcases exists_mem_of_sup_mem_scottOpen hA hs U₂ hs₂ with
            ⟨x₂, hx₂A, hx₂U⟩
          rcases hA.2 hx₁A hx₂A with ⟨x, hxA, hx₁x, hx₂x⟩
          have hxU₁ := Chapter2.scottOpen_upper U₁.scott_open hx₁U hx₁x
          have hxU₂ := Chapter2.scottOpen_upper U₂.scott_open hx₂U hx₂x
          simpa [Figure11PairFunction, hs₁, hs₂, hxU₁, hxU₂] using
            hy ⟨x, hxA, rfl⟩
        · rcases exists_mem_of_sup_mem_scottOpen hA hs U₁ hs₁ with
            ⟨x, hxA, hxU₁⟩
          have hxNotU₂ : x ∉ U₂.carrierSet := by
            intro hxU₂
            exact hs₂ (Chapter2.scottOpen_upper U₂.scott_open hxU₂ (hs.1 hxA))
          simpa [Figure11PairFunction, hs₁, hs₂, hxU₁, hxNotU₂] using
            hy ⟨x, hxA, rfl⟩
      · by_cases hs₂ : s ∈ U₂.carrierSet
        · rcases exists_mem_of_sup_mem_scottOpen hA hs U₂ hs₂ with
            ⟨x, hxA, hxU₂⟩
          have hxNotU₁ : x ∉ U₁.carrierSet := by
            intro hxU₁
            exact hs₁ (Chapter2.scottOpen_upper U₁.scott_open hxU₁ (hs.1 hxA))
          simpa [Figure11PairFunction, hs₁, hs₂, hxNotU₁, hxU₂] using
            hy ⟨x, hxA, rfl⟩
        · simpa [Figure11PairFunction, hs₁, hs₂] using hX.bottom_le y

/-- Bundled form of the Figure 11 four-region map. -/
noncomputable def Figure11PairContFun
    {D : Type u} [Preorder D] {X : OrderedDomain.{u}}
    (hX : Figure11XDiagram X) (joint : Fin 6)
    (hjoint : joint = 3 ∨ joint = 4 ∨ joint = 5)
    (U₁ U₂ : ScottOpenCarrier
      ({ carrier := D, preorder := inferInstance } : OrderedDomain)) :
    Chapter3.ContFun D X.carrier where
  toFun := Figure11PairFunction hX joint U₁ U₂
  continuous := figure11PairFunction_scottContinuous hX hjoint U₁ U₂

/-- Noncoherence supplies exactly the three Scott opens used in the source
proof of Lemma 4.3.1. -/
theorem exists_scottOpen_noncoherence_witness
    (D : OrderedDomain.{u}) (hD : IsContinuousDomainObject D)
    (hNotCoherent : ¬ IsCoherentDomain D) :
    ∃ O U₁ U₂ : ScottOpenCarrier D,
      ScottOpenWayBelow D O U₁ ∧
        ScottOpenWayBelow D O U₂ ∧
          ¬ ScottOpenWayBelow D O (ScottOpenCarrier.inter D U₁ U₂) := by
  have hNotProperty : ¬ ScottOpenIntersectionWayBelowProperty D := by
    intro hProperty
    exact hNotCoherent
      ((prop_4_2_16_coherence_open_neighborhoods D hD.1 hD.2).2 hProperty)
  simp only [ScottOpenIntersectionWayBelowProperty] at hNotProperty
  push Not at hNotProperty
  exact hNotProperty

/-- The failed way-below relation yields a directed open family above the
intersection but with no member covering `O`. -/
theorem exists_directed_open_family_not_covering
    (D : OrderedDomain.{u})
    {O U : ScottOpenCarrier D} (hNot : ¬ ScottOpenWayBelow D O U) :
    ∃ (A : Set (ScottOpenCarrier D)) (s : ScottOpenCarrier D),
      Chapter3.DirectedSet A ∧ Chapter3.IsSup A s ∧ U ≤ s ∧
        ∀ V ∈ A, ¬ O ≤ V := by
  rw [ScottOpenWayBelow] at hNot
  simp only [Chapter2.WayBelow] at hNot
  push Not at hNot
  rcases hNot with ⟨A, s, hA, hs, hUs, hNo⟩
  exact ⟨A, s, hA, hs, hUs, by
    intro V hVA hOV
    exact hNo V hVA hOV⟩

namespace Figure11XDiagram

theorem eq_c₁_of_left_right_le_of_le_c₁
    {X : OrderedDomain.{u}} (hX : Figure11XDiagram X) {x : X.carrier}
    (hleft : hX.point 1 ≤ x) (hright : hX.point 2 ≤ x)
    (hc₁ : x ≤ hX.point 3) : x = hX.point 3 := by
  rcases hX.point_bijective.2 x with ⟨i, rfl⟩
  have hleft' := (hX.order_iff 1 i).1 hleft
  have hright' := (hX.order_iff 2 i).1 hright
  have hc₁' := (hX.order_iff i 3).1 hc₁
  have hi : i = 3 := by
    fin_cases i <;> simp_all [Figure11XLe]
  exact congrArg hX.point hi

theorem not_c₁_le_c₂ {X : OrderedDomain.{u}} (hX : Figure11XDiagram X) :
    ¬ hX.point 3 ≤ hX.point 4 := by
  rw [hX.order_iff]
  simp [Figure11XLe]

theorem c₂_le_top {X : OrderedDomain.{u}} (hX : Figure11XDiagram X) :
    hX.point 4 ≤ hX.point 5 :=
  (hX.order_iff 4 5).2 (by simp [Figure11XLe])

end Figure11XDiagram

/-- Open-step map into Figure 11's `X`, using its displayed bottom point. -/
noncomputable def Figure11OpenStepContFun
    {D : Type u} [Preorder D] {X : OrderedDomain.{u}}
    (hX : Figure11XDiagram X)
    (O : ScottOpenCarrier
      ({ carrier := D, preorder := inferInstance } : OrderedDomain))
    (i : Fin 6) : Chapter3.ContFun D X.carrier := by
  letI : OrderBot X.carrier := hX.orderBot
  exact OpenStepContFun O (hX.point i)

theorem openStep_left_le_figure11Pair
    {D : Type u} [Preorder D] {X : OrderedDomain.{u}}
    (hX : Figure11XDiagram X) (hXdcpo : Chapter3.IsDcpo X.carrier)
    (O U₁ U₂ : ScottOpenCarrier
      ({ carrier := D, preorder := inferInstance } : OrderedDomain))
    (hOU₁ : Chapter3.WayBelow O U₁) :
    Figure11OpenStepContFun hX O 1 ≪
      Figure11PairContFun hX 3 (Or.inl rfl) U₁ U₂ := by
  letI : OrderBot X.carrier := hX.orderBot
  change OpenStepContFun O (hX.point 1) ≪
    Figure11PairContFun hX 3 (Or.inl rfl) U₁ U₂
  apply openStepContFun_wayBelow hXdcpo (hX.point_compact 1) hOU₁
  intro x
  by_cases hx₁ : x ∈ U₁.carrierSet
  · by_cases hx₂ : x ∈ U₂.carrierSet
    · simpa [OpenStepContFun, OpenStepFunction, Figure11PairContFun,
        Figure11PairFunction, hx₁, hx₂] using
        hX.left_le_joint (j := (3 : Fin 6)) (Or.inl rfl)
    · simp [OpenStepContFun, OpenStepFunction, Figure11PairContFun,
        Figure11PairFunction, hx₁, hx₂]
  · simp [OpenStepContFun, OpenStepFunction, Figure11PairContFun,
      Figure11PairFunction, hx₁]

theorem openStep_right_le_figure11Pair
    {D : Type u} [Preorder D] {X : OrderedDomain.{u}}
    (hX : Figure11XDiagram X) (hXdcpo : Chapter3.IsDcpo X.carrier)
    (O U₁ U₂ : ScottOpenCarrier
      ({ carrier := D, preorder := inferInstance } : OrderedDomain))
    (hOU₂ : Chapter3.WayBelow O U₂) :
    Figure11OpenStepContFun hX O 2 ≪
      Figure11PairContFun hX 3 (Or.inl rfl) U₁ U₂ := by
  letI : OrderBot X.carrier := hX.orderBot
  change OpenStepContFun O (hX.point 2) ≪
    Figure11PairContFun hX 3 (Or.inl rfl) U₁ U₂
  apply openStepContFun_wayBelow hXdcpo (hX.point_compact 2) hOU₂
  intro x
  by_cases hx₁ : x ∈ U₁.carrierSet
  · by_cases hx₂ : x ∈ U₂.carrierSet
    · simpa [OpenStepContFun, OpenStepFunction, Figure11PairContFun,
        Figure11PairFunction, hx₁, hx₂] using
        hX.right_le_joint (j := (3 : Fin 6)) (Or.inl rfl)
    · simp [OpenStepContFun, OpenStepFunction, Figure11PairContFun,
        Figure11PairFunction, hx₁, hx₂]
  · by_cases hx₂ : x ∈ U₂.carrierSet
    · simp [OpenStepContFun, OpenStepFunction, Figure11PairContFun,
        Figure11PairFunction, hx₁, hx₂]
    · simp [OpenStepContFun, OpenStepFunction, Figure11PairContFun,
        Figure11PairFunction, hx₁, hx₂]

theorem figure11Pair_c₁_le_top
    {D : Type u} [Preorder D] {X : OrderedDomain.{u}}
    (hX : Figure11XDiagram X)
    (U₁ U₂ : ScottOpenCarrier
      ({ carrier := D, preorder := inferInstance } : OrderedDomain)) :
    Figure11PairContFun hX 3 (Or.inl rfl) U₁ U₂ ≤
      Figure11PairContFun hX 5 (Or.inr (Or.inr rfl)) U₁ U₂ := by
  intro x
  by_cases hx₁ : x ∈ U₁.carrierSet <;>
    by_cases hx₂ : x ∈ U₂.carrierSet <;>
      simp [Figure11PairContFun, Figure11PairFunction, hx₁, hx₂,
        hX.order_iff, Figure11XLe]

end Chapter4
end AbramskyJung

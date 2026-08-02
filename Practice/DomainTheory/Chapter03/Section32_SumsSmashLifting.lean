import Practice.DomainTheory.Chapter03.Section32_Products

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 3.2: sums, smash products, and lifting

This file formalizes the coalesced-sum carrier, order, pointed-dcpo
construction, carrier-level strict eliminator, strict Scott-continuity clauses,
and continuous/algebraic object-class closure support needed for Proposition
3.2.9.  It also records the foundational smash-product carrier/order data used
by the strict-pointed monoidal-closed interface in Theorem 3.3.4, including
Scott-continuity of the smash-product introduction map and the pointed-dcpo
carrier package.
-/

universe u v w

namespace AbramskyJung
namespace Chapter3

section SumsSmashLifting

variable (D : Type u) (E : Type v)
variable [Preorder D] [Preorder E]

/-- Section 3.2.3: disjoint union of dcpo carriers. -/
abbrev DisjointSum := Sum D E

variable [OrderBot D] [OrderBot E]

/-- Section 3.2.3: coalesced sum of pointed carriers, with the two bottoms
identified as the single constructor `bot`; non-bottom elements remember which
summand they came from. -/
inductive CoalescedSum where
  | bot : CoalescedSum
  | inl : (x : D) → x ≠ ⊥ → CoalescedSum
  | inr : (y : E) → y ≠ ⊥ → CoalescedSum

namespace CoalescedSum

/-- Order on the coalesced sum: the identified bottom is below everything, and
the two non-bottom summands keep their original orders without adding cross
comparisons. -/
protected def le : CoalescedSum D E → CoalescedSum D E → Prop
  | bot, _ => True
  | inl x _, inl y _ => x ≤ y
  | inr x _, inr y _ => x ≤ y
  | _, _ => False

instance : Preorder (CoalescedSum D E) where
  le := CoalescedSum.le (D := D) (E := E)
  le_refl x := by
    cases x <;> simp [CoalescedSum.le]
  le_trans x y z hxy hyz := by
    cases x <;> cases y <;> cases z <;> simp only [CoalescedSum.le] at hxy hyz ⊢
    all_goals exact le_trans hxy hyz

instance : OrderBot (CoalescedSum D E) where
  bot := bot
  bot_le x := by
    change CoalescedSum.le (D := D) (E := E) bot x
    cases x <;> simp [CoalescedSum.le]

/-- Left injection into the coalesced sum: bottom is sent to the identified
bottom, and non-bottom elements are tagged as left summand elements. -/
noncomputable def inl' (x : D) : CoalescedSum D E := by
  classical
  exact if hx : x = ⊥ then bot else inl x hx

/-- Right injection into the coalesced sum: bottom is sent to the identified
bottom, and non-bottom elements are tagged as right summand elements. -/
noncomputable def inr' (y : E) : CoalescedSum D E := by
  classical
  exact if hy : y = ⊥ then bot else inr y hy

@[simp] theorem inl'_bot : inl' (D := D) (E := E) ⊥ = (⊥ : CoalescedSum D E) := by
  change inl' (D := D) (E := E) ⊥ = bot
  simp [inl']

@[simp] theorem inr'_bot : inr' (D := D) (E := E) ⊥ = (⊥ : CoalescedSum D E) := by
  change inr' (D := D) (E := E) ⊥ = bot
  simp [inr']

theorem inl'_of_ne {x : D} (hx : x ≠ ⊥) :
    inl' (D := D) (E := E) x = inl x hx := by
  simp [inl', hx]

theorem inr'_of_ne {y : E} (hy : y ≠ ⊥) :
    inr' (D := D) (E := E) y = inr y hy := by
  simp [inr', hy]

/-- The coalesced-sum bottom is least. -/
theorem bot_isLeast : Chapter2.IsLeast (⊥ : CoalescedSum D E) := by
  intro x
  exact bot_le

/-- Left injection is strict. -/
theorem inl_strict : Chapter2.StrictMap (inl' (D := D) (E := E)) :=
  inl'_bot (D := D) (E := E)

/-- Right injection is strict. -/
theorem inr_strict : Chapter2.StrictMap (inr' (D := D) (E := E)) :=
  inr'_bot (D := D) (E := E)

/-- Coalesced-sum eliminator for strict maps. -/
noncomputable def desc {F : Type w} [Preorder F] [OrderBot F]
    (f : D → F) (g : E → F) : CoalescedSum D E → F
  | bot => ⊥
  | inl x _ => f x
  | inr y _ => g y

theorem desc_strict {F : Type w} [Preorder F] [OrderBot F] (f : D → F) (g : E → F) :
    Chapter2.StrictMap (desc (D := D) (E := E) f g) := rfl

theorem desc_inl {F : Type w} [Preorder F] [OrderBot F] {f : D → F} {g : E → F}
    (hf : Chapter2.StrictMap f) (x : D) :
    desc (D := D) (E := E) f g (inl' (D := D) (E := E) x) = f x := by
  classical
  by_cases hx : x = ⊥
  · simp [inl', hx, desc, hf.symm]
  · simp [inl', hx, desc]

theorem desc_inr {F : Type w} [Preorder F] [OrderBot F] {f : D → F} {g : E → F}
    (hg : Chapter2.StrictMap g) (y : E) :
    desc (D := D) (E := E) f g (inr' (D := D) (E := E) y) = g y := by
  classical
  by_cases hy : y = ⊥
  · simp [inr', hy, desc, hg.symm]
  · simp [inr', hy, desc]

theorem desc_unique {F : Type w} [Preorder F] [OrderBot F] {f : D → F} {g : E → F}
    {h : CoalescedSum D E → F}
    (hh : Chapter2.StrictMap h)
    (hinl : ∀ x : D, h (inl' (D := D) (E := E) x) = f x)
    (hinr : ∀ y : E, h (inr' (D := D) (E := E) y) = g y) :
    ∀ z : CoalescedSum D E, h z = desc (D := D) (E := E) f g z := by
  intro z
  cases z with
  | bot => exact hh
  | inl x hx =>
      simpa [inl'_of_ne (D := D) (E := E) hx, desc] using hinl x
  | inr y hy =>
      simpa [inr'_of_ne (D := D) (E := E) hy, desc] using hinr y

/-- The left injection is monotone when the source bottom is separated from
non-bottom points.  In a bundled poset this is automatic from antisymmetry. -/
theorem inl_monotone (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥) :
    Monotone (inl' (D := D) (E := E)) := by
  classical
  intro x y hxy
  by_cases hx : x = ⊥
  · subst x
    rw [inl'_bot (D := D) (E := E)]
    exact (bot_le : (⊥ : CoalescedSum D E) ≤ inl' (D := D) (E := E) y)
  · by_cases hy : y = ⊥
    · exact False.elim (hx (hDbot x (by simpa [hy] using hxy)))
    · simpa [inl', hx, hy, CoalescedSum.le] using hxy

/-- The right injection is monotone when the source bottom is separated from
non-bottom points.  In a bundled poset this is automatic from antisymmetry. -/
theorem inr_monotone (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    Monotone (inr' (D := D) (E := E)) := by
  classical
  intro x y hxy
  by_cases hx : x = ⊥
  · subst x
    rw [inr'_bot (D := D) (E := E)]
    exact (bot_le : (⊥ : CoalescedSum D E) ≤ inr' (D := D) (E := E) y)
  · by_cases hy : y = ⊥
    · exact False.elim (hx (hEbot x (by simpa [hy] using hxy)))
    · simpa [inr', hx, hy, CoalescedSum.le] using hxy

/-- The left injection into the coalesced sum is Scott-continuous. -/
theorem inl_scottContinuous (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥) :
    ScottContinuous (inl' (D := D) (E := E)) := by
  classical
  constructor
  · exact inl_monotone (D := D) (E := E) hDbot
  · intro A x hA hx
    constructor
    · intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact inl_monotone (D := D) (E := E) hDbot (hx.1 ha)
    · intro y hy
      by_cases hxbot : x = ⊥
      · subst x
        rw [inl'_bot (D := D) (E := E)]
        exact (bot_le : (⊥ : CoalescedSum D E) ≤ y)
      · cases y with
        | bot =>
            have all_bot : ∀ a : D, a ∈ A → a = ⊥ := by
              intro a ha
              by_contra hane
              have hle : inl' (D := D) (E := E) a ≤ (⊥ : CoalescedSum D E) :=
                hy ⟨a, ha, rfl⟩
              exact (by
                simpa [inl'_of_ne (D := D) (E := E) hane, CoalescedSum.le] using hle)
            have hbotUpper : IsUpperBound A (⊥ : D) := by
              intro a ha
              simpa [all_bot a ha]
            exact False.elim (hxbot (hDbot x (hx.2 ⊥ hbotUpper)))
        | inl y hyne =>
            have hyUpper : IsUpperBound A y := by
              intro a ha
              by_cases habot : a = ⊥
              · simpa [habot]
              · have hle : inl' (D := D) (E := E) a ≤ CoalescedSum.inl y hyne :=
                  hy ⟨a, ha, rfl⟩
                simpa [inl'_of_ne (D := D) (E := E) habot, CoalescedSum.le] using hle
            have hxle : x ≤ y := hx.2 y hyUpper
            simpa [inl'_of_ne (D := D) (E := E) hxbot, CoalescedSum.le] using hxle
        | inr y hyne =>
            have hnonbot : ∃ a : D, a ∈ A ∧ a ≠ ⊥ := by
              by_contra hnone
              have all_bot : ∀ a : D, a ∈ A → a = ⊥ := by
                intro a ha
                by_contra hane
                exact hnone ⟨a, ha, hane⟩
              have hbotUpper : IsUpperBound A (⊥ : D) := by
                intro a ha
                simpa [all_bot a ha]
              exact hxbot (hDbot x (hx.2 ⊥ hbotUpper))
            rcases hnonbot with ⟨a, ha, hane⟩
            have hle : inl' (D := D) (E := E) a ≤ CoalescedSum.inr y hyne :=
              hy ⟨a, ha, rfl⟩
            exact False.elim (by
              simpa [inl'_of_ne (D := D) (E := E) hane, CoalescedSum.le] using hle)

/-- The right injection into the coalesced sum is Scott-continuous. -/
theorem inr_scottContinuous (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    ScottContinuous (inr' (D := D) (E := E)) := by
  classical
  constructor
  · exact inr_monotone (D := D) (E := E) hEbot
  · intro A y hA hy
    constructor
    · intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact inr_monotone (D := D) (E := E) hEbot (hy.1 ha)
    · intro x hx
      by_cases hybot : y = ⊥
      · subst y
        rw [inr'_bot (D := D) (E := E)]
        exact (bot_le : (⊥ : CoalescedSum D E) ≤ x)
      · cases x with
        | bot =>
            have all_bot : ∀ a : E, a ∈ A → a = ⊥ := by
              intro a ha
              by_contra hane
              have hle : inr' (D := D) (E := E) a ≤ (⊥ : CoalescedSum D E) :=
                hx ⟨a, ha, rfl⟩
              exact (by
                simpa [inr'_of_ne (D := D) (E := E) hane, CoalescedSum.le] using hle)
            have hbotUpper : IsUpperBound A (⊥ : E) := by
              intro a ha
              simpa [all_bot a ha]
            exact False.elim (hybot (hEbot y (hy.2 ⊥ hbotUpper)))
        | inl x hxne =>
            have hnonbot : ∃ a : E, a ∈ A ∧ a ≠ ⊥ := by
              by_contra hnone
              have all_bot : ∀ a : E, a ∈ A → a = ⊥ := by
                intro a ha
                by_contra hane
                exact hnone ⟨a, ha, hane⟩
              have hbotUpper : IsUpperBound A (⊥ : E) := by
                intro a ha
                simpa [all_bot a ha]
              exact hybot (hEbot y (hy.2 ⊥ hbotUpper))
            rcases hnonbot with ⟨a, ha, hane⟩
            have hle : inr' (D := D) (E := E) a ≤ CoalescedSum.inl x hxne :=
              hx ⟨a, ha, rfl⟩
            exact False.elim (by
              simpa [inr'_of_ne (D := D) (E := E) hane, CoalescedSum.le] using hle)
        | inr x hxne =>
            have hxUpper : IsUpperBound A x := by
              intro a ha
              by_cases habot : a = ⊥
              · simpa [habot]
              · have hle : inr' (D := D) (E := E) a ≤ CoalescedSum.inr x hxne :=
                  hx ⟨a, ha, rfl⟩
                simpa [inr'_of_ne (D := D) (E := E) habot, CoalescedSum.le] using hle
            have hyle : y ≤ x := hy.2 x hxUpper
            simpa [inr'_of_ne (D := D) (E := E) hybot, CoalescedSum.le] using hyle

/-- The strict eliminator is monotone whenever the two component maps are. -/
theorem desc_monotone {F : Type w} [Preorder F] [OrderBot F] {f : D → F} {g : E → F}
    (hf : Monotone f) (hg : Monotone g) :
    Monotone (desc (D := D) (E := E) f g) := by
  intro x y hxy
  cases x with
  | bot =>
      cases y <;> exact bot_le
  | inl x hx =>
      cases y with
      | bot =>
          exact False.elim (by simpa [CoalescedSum.le] using hxy)
      | inl y hy =>
          exact hf (by simpa [CoalescedSum.le] using hxy)
      | inr y hy =>
          exact False.elim (by simpa [CoalescedSum.le] using hxy)
  | inr x hx =>
      cases y with
      | bot =>
          exact False.elim (by simpa [CoalescedSum.le] using hxy)
      | inl y hy =>
          exact False.elim (by simpa [CoalescedSum.le] using hxy)
      | inr y hy =>
          exact hg (by simpa [CoalescedSum.le] using hxy)

/-- If `A` has a left-summand supremum in the coalesced sum, then the
corresponding set of left coordinates has the matching supremum in `D`. -/
theorem leftValues_isSup
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    {A : Set (CoalescedSum D E)} {x : D} {hxne : x ≠ ⊥}
    (hx : IsSup A (CoalescedSum.inl x hxne)) :
    IsSup ({d : D | d = ⊥ ∨ ∃ hd : d ≠ ⊥, CoalescedSum.inl d hd ∈ A}) x := by
  constructor
  · intro d hd
    rcases hd with rfl | ⟨hdne, hdA⟩
    · exact bot_le
    · have hle : CoalescedSum.inl d hdne ≤ CoalescedSum.inl x hxne := hx.1 hdA
      simpa [CoalescedSum.le] using hle
  · intro y hy
    have hUpper : IsUpperBound A (inl' (D := D) (E := E) y) := by
      intro a ha
      cases a with
      | bot => exact bot_le
      | inl d hdne =>
          by_cases hybot : y = ⊥
          · have hdy : d ≤ y := by
              simpa [hybot] using hy (Or.inr ⟨hdne, ha⟩)
            exact False.elim (hdne (hDbot d (by simpa [hybot] using hdy)))
          · have hdy : d ≤ y := hy (Or.inr ⟨hdne, ha⟩)
            simpa [inl'_of_ne (D := D) (E := E) hybot, CoalescedSum.le] using hdy
      | inr e hene =>
          have hle : CoalescedSum.inr e hene ≤ CoalescedSum.inl x hxne := hx.1 ha
          exact False.elim (by simpa [CoalescedSum.le] using hle)
    have hxy : CoalescedSum.inl x hxne ≤ inl' (D := D) (E := E) y := hx.2 _ hUpper
    by_cases hybot : y = ⊥
    · exact False.elim (by simpa [inl', hybot, CoalescedSum.le] using hxy)
    · simpa [inl'_of_ne (D := D) (E := E) hybot, CoalescedSum.le] using hxy

/-- If `A` has a right-summand supremum in the coalesced sum, then the
corresponding set of right coordinates has the matching supremum in `E`. -/
theorem rightValues_isSup
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    {A : Set (CoalescedSum D E)} {y : E} {hyne : y ≠ ⊥}
    (hy : IsSup A (CoalescedSum.inr y hyne)) :
    IsSup ({e : E | e = ⊥ ∨ ∃ he : e ≠ ⊥, CoalescedSum.inr e he ∈ A}) y := by
  constructor
  · intro e he
    rcases he with rfl | ⟨hene, heA⟩
    · exact bot_le
    · have hle : CoalescedSum.inr e hene ≤ CoalescedSum.inr y hyne := hy.1 heA
      simpa [CoalescedSum.le] using hle
  · intro z hz
    have hUpper : IsUpperBound A (inr' (D := D) (E := E) z) := by
      intro a ha
      cases a with
      | bot => exact bot_le
      | inl d hdne =>
          have hle : CoalescedSum.inl d hdne ≤ CoalescedSum.inr y hyne := hy.1 ha
          exact False.elim (by simpa [CoalescedSum.le] using hle)
      | inr e hene =>
          by_cases hzbot : z = ⊥
          · have hez : e ≤ z := by
              simpa [hzbot] using hz (Or.inr ⟨hene, ha⟩)
            exact False.elim (hene (hEbot e (by simpa [hzbot] using hez)))
          · have hez : e ≤ z := hz (Or.inr ⟨hene, ha⟩)
            simpa [inr'_of_ne (D := D) (E := E) hzbot, CoalescedSum.le] using hez
    have hyz : CoalescedSum.inr y hyne ≤ inr' (D := D) (E := E) z := hy.2 _ hUpper
    by_cases hzbot : z = ⊥
    · exact False.elim (by simpa [inr', hzbot, CoalescedSum.le] using hyz)
    · simpa [inr'_of_ne (D := D) (E := E) hzbot, CoalescedSum.le] using hyz

/-- The left-coordinate set of a directed coalesced-sum family is directed. -/
theorem leftValues_directed {A : Set (CoalescedSum D E)} (hA : DirectedSet A) :
    DirectedSet ({d : D | d = ⊥ ∨ ∃ hd : d ≠ ⊥, CoalescedSum.inl d hd ∈ A}) := by
  constructor
  · exact ⟨⊥, Or.inl rfl⟩
  · intro x hx y hy
    rcases hx with rfl | ⟨hxne, hxA⟩
    · exact ⟨y, hy, bot_le, le_rfl⟩
    rcases hy with rfl | ⟨hyne, hyA⟩
    · exact ⟨x, Or.inr ⟨hxne, hxA⟩, le_rfl, bot_le⟩
    rcases hA.2 hxA hyA with ⟨z, hzA, hxz, hyz⟩
    cases z with
    | bot => exact False.elim (by simpa [CoalescedSum.le] using hxz)
    | inl z hz =>
        exact ⟨z, Or.inr ⟨hz, hzA⟩,
          by simpa [CoalescedSum.le] using hxz,
          by simpa [CoalescedSum.le] using hyz⟩
    | inr z hz => exact False.elim (by simpa [CoalescedSum.le] using hxz)

/-- The right-coordinate set of a directed coalesced-sum family is directed. -/
theorem rightValues_directed {A : Set (CoalescedSum D E)} (hA : DirectedSet A) :
    DirectedSet ({e : E | e = ⊥ ∨ ∃ he : e ≠ ⊥, CoalescedSum.inr e he ∈ A}) := by
  constructor
  · exact ⟨⊥, Or.inl rfl⟩
  · intro x hx y hy
    rcases hx with rfl | ⟨hxne, hxA⟩
    · exact ⟨y, hy, bot_le, le_rfl⟩
    rcases hy with rfl | ⟨hyne, hyA⟩
    · exact ⟨x, Or.inr ⟨hxne, hxA⟩, le_rfl, bot_le⟩
    rcases hA.2 hxA hyA with ⟨z, hzA, hxz, hyz⟩
    cases z with
    | bot => exact False.elim (by simpa [CoalescedSum.le] using hxz)
    | inl z hz => exact False.elim (by simpa [CoalescedSum.le] using hxz)
    | inr z hz =>
        exact ⟨z, Or.inr ⟨hz, hzA⟩,
          by simpa [CoalescedSum.le] using hxz,
          by simpa [CoalescedSum.le] using hyz⟩

/-- The identified bottom is way-below every point of the coalesced sum. -/
theorem bot_wayBelow (z : CoalescedSum D E) : WayBelow (⊥ : CoalescedSum D E) z := by
  intro A s hA _hs _hzs
  rcases hA.1 with ⟨a, ha⟩
  exact ⟨a, ha, bot_le⟩

/-- Way-below in the left summand transfers to way-below in the coalesced sum.
This is one of the local ingredients needed for the `CONT⊥!` object-closure
part of Proposition 3.2.9. -/
theorem inl_wayBelow_of_wayBelow
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    {a x : D} (ha_ne : a ≠ ⊥) (hx_ne : x ≠ ⊥) (hax : WayBelow a x) :
    @WayBelow (CoalescedSum D E) inferInstance
      (CoalescedSum.inl a ha_ne) (CoalescedSum.inl x hx_ne) := by
  intro A s hA hs hxs
  cases s with
  | bot =>
      exact False.elim (by simpa [CoalescedSum.le] using hxs)
  | inl y hy =>
      have hxy : x ≤ y := by
        simpa [CoalescedSum.le] using hxs
      have hLeftSup :
          IsSup ({d : D | d = ⊥ ∨ ∃ hd : d ≠ ⊥, CoalescedSum.inl d hd ∈ A}) y :=
        leftValues_isSup (D := D) (E := E) hDbot hs
      have hLeftDir :
          DirectedSet ({d : D | d = ⊥ ∨ ∃ hd : d ≠ ⊥, CoalescedSum.inl d hd ∈ A}) :=
        leftValues_directed (D := D) (E := E) hA
      have hay : WayBelow a y := wayBelow_mono le_rfl hax hxy
      rcases hay hLeftDir hLeftSup le_rfl with ⟨d, hd, had⟩
      rcases hd with rfl | ⟨hdne, hdA⟩
      · exact False.elim (ha_ne (hDbot a had))
      · exact ⟨CoalescedSum.inl d hdne, hdA, by simpa [CoalescedSum.le] using had⟩
  | inr y hy =>
      exact False.elim (by simpa [CoalescedSum.le] using hxs)

/-- Way-below in the right summand transfers to way-below in the coalesced sum.
This is one of the local ingredients needed for the `CONT⊥!` object-closure
part of Proposition 3.2.9. -/
theorem inr_wayBelow_of_wayBelow
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    {a y : E} (ha_ne : a ≠ ⊥) (hy_ne : y ≠ ⊥) (hay : WayBelow a y) :
    @WayBelow (CoalescedSum D E) inferInstance
      (CoalescedSum.inr a ha_ne) (CoalescedSum.inr y hy_ne) := by
  intro A s hA hs hys
  cases s with
  | bot =>
      exact False.elim (by simpa [CoalescedSum.le] using hys)
  | inl x hx =>
      exact False.elim (by simpa [CoalescedSum.le] using hys)
  | inr z hz =>
      have hyz : y ≤ z := by
        simpa [CoalescedSum.le] using hys
      have hRightSup :
          IsSup ({e : E | e = ⊥ ∨ ∃ he : e ≠ ⊥, CoalescedSum.inr e he ∈ A}) z :=
        rightValues_isSup (D := D) (E := E) hEbot hs
      have hRightDir :
          DirectedSet ({e : E | e = ⊥ ∨ ∃ he : e ≠ ⊥, CoalescedSum.inr e he ∈ A}) :=
        rightValues_directed (D := D) (E := E) hA
      have haz : WayBelow a z := wayBelow_mono le_rfl hay hyz
      rcases haz hRightDir hRightSup le_rfl with ⟨e, he, hae⟩
      rcases he with rfl | ⟨hene, heA⟩
      · exact False.elim (ha_ne (hEbot a hae))
      · exact ⟨CoalescedSum.inr e hene, heA, by simpa [CoalescedSum.le] using hae⟩

/-- Candidate basis for the coalesced sum built from bases in the two summands. -/
def continuousBasis (BD : Set D) (BE : Set E) : Set (CoalescedSum D E) :=
  {z | z = ⊥ ∨
    (∃ (x : D) (hx : x ≠ ⊥), x ∈ BD ∧ z = CoalescedSum.inl x hx) ∨
      (∃ (y : E) (hy : y ≠ ⊥), y ∈ BE ∧ z = CoalescedSum.inr y hy)}

/-- The coalesced-sum basis generated from summand bases is a raw basis. -/
theorem continuousBasis_isBasisRaw
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    {BD : Set D} {BE : Set E} (hBD : IsBasis BD) (hBE : IsBasis BE) :
    Chapter2.IsBasisRaw (continuousBasis (D := D) (E := E) BD BE) := by
  intro z
  cases z with
  | bot =>
      refine ⟨{⊥}, ?_, Chapter2.directed_singleton (⊥ : CoalescedSum D E),
        Chapter2.isSup_singleton (⊥ : CoalescedSum D E)⟩
      intro a ha
      have haeq : a = (⊥ : CoalescedSum D E) := by simpa using ha
      subst a
      exact ⟨Or.inl rfl, bot_wayBelow (D := D) (E := E) (⊥ : CoalescedSum D E)⟩
  | inl x hxne =>
      refine ⟨inl' (D := D) (E := E) '' Approximants BD x, ?_, ?_, ?_⟩
      · intro a ha
        rcases ha with ⟨b, hb, rfl⟩
        rcases hb with ⟨hbBD, hbwx⟩
        by_cases hbbot : b = ⊥
        · subst b
          rw [inl'_bot (D := D) (E := E)]
          exact ⟨Or.inl rfl, bot_wayBelow (D := D) (E := E) (CoalescedSum.inl x hxne)⟩
        · rw [inl'_of_ne (D := D) (E := E) hbbot]
          exact
            ⟨Or.inr (Or.inl ⟨b, hbbot, hbBD, rfl⟩),
              inl_wayBelow_of_wayBelow (D := D) (E := E) hDbot hbbot hxne hbwx⟩
      · exact DirectedSet.image (inl_monotone (D := D) (E := E) hDbot) (hBD x).1
      · have hsup :
            IsSup (inl' (D := D) (E := E) '' Approximants BD x)
              (inl' (D := D) (E := E) x) :=
          (inl_scottContinuous (D := D) (E := E) hDbot).2 (hBD x).1 (hBD x).2
        simpa [inl'_of_ne (D := D) (E := E) hxne] using hsup
  | inr y hyne =>
      refine ⟨inr' (D := D) (E := E) '' Approximants BE y, ?_, ?_, ?_⟩
      · intro a ha
        rcases ha with ⟨b, hb, rfl⟩
        rcases hb with ⟨hbBE, hbwy⟩
        by_cases hbbot : b = ⊥
        · subst b
          rw [inr'_bot (D := D) (E := E)]
          exact ⟨Or.inl rfl, bot_wayBelow (D := D) (E := E) (CoalescedSum.inr y hyne)⟩
        · rw [inr'_of_ne (D := D) (E := E) hbbot]
          exact
            ⟨Or.inr (Or.inr ⟨b, hbbot, hbBE, rfl⟩),
              inr_wayBelow_of_wayBelow (D := D) (E := E) hEbot hbbot hyne hbwy⟩
      · exact DirectedSet.image (inr_monotone (D := D) (E := E) hEbot) (hBE y).1
      · have hsup :
            IsSup (inr' (D := D) (E := E) '' Approximants BE y)
              (inr' (D := D) (E := E) y) :=
          (inr_scottContinuous (D := D) (E := E) hEbot).2 (hBE y).1 (hBE y).2
        simpa [inr'_of_ne (D := D) (E := E) hyne] using hsup

/-- The coalesced sum of continuous pointed dcpos is continuous. -/
theorem continuousDomain
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    (hD : IsContinuousDomain D) (hE : IsContinuousDomain E) :
    IsContinuousDomain (CoalescedSum D E) := by
  rcases hD with ⟨BD, hBD⟩
  rcases hE with ⟨BE, hBE⟩
  exact ⟨continuousBasis (D := D) (E := E) BD BE,
    Chapter2.prop_2_2_4_1
      (continuousBasis_isBasisRaw (D := D) (E := E) hDbot hEbot hBD hBE)⟩

/-- The identified bottom is compact in the coalesced sum. -/
theorem bot_compact : Compact (⊥ : CoalescedSum D E) :=
  bot_wayBelow (D := D) (E := E) (⊥ : CoalescedSum D E)

/-- Compactness in the left summand transfers to compactness in the coalesced
sum. -/
theorem inl_compact_of_compact
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    {a : D} (ha_ne : a ≠ ⊥) (ha : Compact a) :
    Compact (CoalescedSum.inl a ha_ne : CoalescedSum D E) :=
  inl_wayBelow_of_wayBelow (D := D) (E := E) hDbot ha_ne ha_ne ha

/-- Compactness in the right summand transfers to compactness in the coalesced
sum. -/
theorem inr_compact_of_compact
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    {a : E} (ha_ne : a ≠ ⊥) (ha : Compact a) :
    Compact (CoalescedSum.inr a ha_ne : CoalescedSum D E) :=
  inr_wayBelow_of_wayBelow (D := D) (E := E) hEbot ha_ne ha_ne ha

/-- The compact elements form a raw basis for the coalesced sum when the compact
elements form bases in both summands. -/
theorem compactBasis_isBasisRaw
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    (hD : IsAlgebraicDomain D) (hE : IsAlgebraicDomain E) :
    Chapter2.IsBasisRaw ({z : CoalescedSum D E | Compact z} : Set (CoalescedSum D E)) := by
  intro z
  cases z with
  | bot =>
      refine ⟨{⊥}, ?_, Chapter2.directed_singleton (⊥ : CoalescedSum D E),
        Chapter2.isSup_singleton (⊥ : CoalescedSum D E)⟩
      intro a ha
      have haeq : a = (⊥ : CoalescedSum D E) := by simpa using ha
      subst a
      exact ⟨bot_compact (D := D) (E := E),
        bot_wayBelow (D := D) (E := E) (⊥ : CoalescedSum D E)⟩
  | inl x hxne =>
      refine ⟨inl' (D := D) (E := E) '' Approximants ({b : D | Compact b} : Set D) x,
        ?_, ?_, ?_⟩
      · intro a ha
        rcases ha with ⟨b, hb, rfl⟩
        rcases hb with ⟨hbCompact, hbwx⟩
        by_cases hbbot : b = ⊥
        · subst b
          rw [inl'_bot (D := D) (E := E)]
          exact ⟨bot_compact (D := D) (E := E),
            bot_wayBelow (D := D) (E := E) (CoalescedSum.inl x hxne)⟩
        · rw [inl'_of_ne (D := D) (E := E) hbbot]
          exact
            ⟨inl_compact_of_compact (D := D) (E := E) hDbot hbbot hbCompact,
              inl_wayBelow_of_wayBelow (D := D) (E := E) hDbot hbbot hxne hbwx⟩
      · exact DirectedSet.image (inl_monotone (D := D) (E := E) hDbot) (hD x).1
      · have hsup :
            IsSup (inl' (D := D) (E := E) '' Approximants ({b : D | Compact b} : Set D) x)
              (inl' (D := D) (E := E) x) :=
          (inl_scottContinuous (D := D) (E := E) hDbot).2 (hD x).1 (hD x).2
        simpa [inl'_of_ne (D := D) (E := E) hxne] using hsup
  | inr y hyne =>
      refine ⟨inr' (D := D) (E := E) '' Approximants ({b : E | Compact b} : Set E) y,
        ?_, ?_, ?_⟩
      · intro a ha
        rcases ha with ⟨b, hb, rfl⟩
        rcases hb with ⟨hbCompact, hbwy⟩
        by_cases hbbot : b = ⊥
        · subst b
          rw [inr'_bot (D := D) (E := E)]
          exact ⟨bot_compact (D := D) (E := E),
            bot_wayBelow (D := D) (E := E) (CoalescedSum.inr y hyne)⟩
        · rw [inr'_of_ne (D := D) (E := E) hbbot]
          exact
            ⟨inr_compact_of_compact (D := D) (E := E) hEbot hbbot hbCompact,
              inr_wayBelow_of_wayBelow (D := D) (E := E) hEbot hbbot hyne hbwy⟩
      · exact DirectedSet.image (inr_monotone (D := D) (E := E) hEbot) (hE y).1
      · have hsup :
            IsSup (inr' (D := D) (E := E) '' Approximants ({b : E | Compact b} : Set E) y)
              (inr' (D := D) (E := E) y) :=
          (inr_scottContinuous (D := D) (E := E) hEbot).2 (hE y).1 (hE y).2
        simpa [inr'_of_ne (D := D) (E := E) hyne] using hsup

/-- The coalesced sum of algebraic pointed dcpos is algebraic. -/
theorem algebraicDomain
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    (hD : IsAlgebraicDomain D) (hE : IsAlgebraicDomain E) :
    IsAlgebraicDomain (CoalescedSum D E) :=
  Chapter2.prop_2_2_4_1 (compactBasis_isBasisRaw (D := D) (E := E) hDbot hEbot hD hE)

/-- The strict coalesced-sum eliminator is Scott-continuous when both component
maps are strict and Scott-continuous. -/
theorem desc_scottContinuous
    {F : Type w} [Preorder F] [OrderBot F] {f : D → F} {g : E → F}
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    (hf : ScottContinuous f) (hg : ScottContinuous g)
    (hfstrict : Chapter2.StrictMap f) (hgstrict : Chapter2.StrictMap g) :
    ScottContinuous (desc (D := D) (E := E) f g) := by
  classical
  constructor
  · exact desc_monotone (D := D) (E := E) hf.1 hg.1
  · intro A s hA hs
    constructor
    · intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact desc_monotone (D := D) (E := E) hf.1 hg.1 (hs.1 ha)
    · intro y hy
      cases s with
      | bot =>
          exact bot_le
      | inl x hxne =>
          let AD : Set D := {d | d = ⊥ ∨ ∃ hd : d ≠ ⊥, CoalescedSum.inl d hd ∈ A}
          have hAD : DirectedSet AD := leftValues_directed (D := D) (E := E) hA
          have hxAD : IsSup AD x :=
            leftValues_isSup (D := D) (E := E) hDbot hs
          have hfsup : IsSup (f '' AD) (f x) := hf.2 hAD hxAD
          have hyUpper : IsUpperBound (f '' AD) y := by
            intro z hz
            rcases hz with ⟨d, hd, rfl⟩
            rcases hd with rfl | ⟨hdne, hdA⟩
            · rw [hfstrict]
              exact bot_le
            · exact hy ⟨CoalescedSum.inl d hdne, hdA, rfl⟩
          exact hfsup.2 y hyUpper
      | inr x hxne =>
          let AE : Set E := {e | e = ⊥ ∨ ∃ he : e ≠ ⊥, CoalescedSum.inr e he ∈ A}
          have hAE : DirectedSet AE := rightValues_directed (D := D) (E := E) hA
          have hxAE : IsSup AE x :=
            rightValues_isSup (D := D) (E := E) hEbot hs
          have hgsup : IsSup (g '' AE) (g x) := hg.2 hAE hxAE
          have hyUpper : IsUpperBound (g '' AE) y := by
            intro z hz
            rcases hz with ⟨e, he, rfl⟩
            rcases he with rfl | ⟨hene, heA⟩
            · rw [hgstrict]
              exact bot_le
            · exact hy ⟨CoalescedSum.inr e hene, heA, rfl⟩
          exact hgsup.2 y hyUpper

/-- Strict coproduct universal-property data at the carrier level.

This records strict injections, strict mediators, and mediator uniqueness for
bottom-preserving maps of preordered carriers. -/
structure StrictCoproductData where
  inl_strict : Chapter2.StrictMap (inl' (D := D) (E := E))
  inr_strict : Chapter2.StrictMap (inr' (D := D) (E := E))
  mediator :
    ∀ (F : Type w) [Preorder F] [OrderBot F] (f : D → F) (g : E → F),
      Chapter2.StrictMap f → Chapter2.StrictMap g → CoalescedSum D E → F
  mediator_strict :
    ∀ (F : Type w) [Preorder F] [OrderBot F] (f : D → F) (g : E → F)
      (hf : Chapter2.StrictMap f) (hg : Chapter2.StrictMap g),
      Chapter2.StrictMap (mediator F f g hf hg)
  mediator_inl :
    ∀ (F : Type w) [Preorder F] [OrderBot F] (f : D → F) (g : E → F)
      (hf : Chapter2.StrictMap f) (hg : Chapter2.StrictMap g) (x : D),
      mediator F f g hf hg (inl' (D := D) (E := E) x) = f x
  mediator_inr :
    ∀ (F : Type w) [Preorder F] [OrderBot F] (f : D → F) (g : E → F)
      (hf : Chapter2.StrictMap f) (hg : Chapter2.StrictMap g) (y : E),
      mediator F f g hf hg (inr' (D := D) (E := E) y) = g y
  mediator_unique :
    ∀ (F : Type w) [Preorder F] [OrderBot F] (f : D → F) (g : E → F)
      (hf : Chapter2.StrictMap f) (hg : Chapter2.StrictMap g)
      (h : CoalescedSum D E → F),
      Chapter2.StrictMap h →
      (∀ x : D, h (inl' (D := D) (E := E) x) = f x) →
      (∀ y : E, h (inr' (D := D) (E := E) y) = g y) →
      ∀ z : CoalescedSum D E, h z = mediator F f g hf hg z

/-- Strict Scott-continuous coproduct data for the `DCPO⊥!` reading of
Proposition 3.2.9.  It adds Scott-continuity of the injections and of the
strict mediator to the carrier-level universal property. -/
structure StrictContinuousCoproductData
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) extends StrictCoproductData (D := D) (E := E) where
  inl_continuous : ScottContinuous (inl' (D := D) (E := E))
  inr_continuous : ScottContinuous (inr' (D := D) (E := E))
  mediator_continuous :
    ∀ (F : Type w) [Preorder F] [OrderBot F] (f : D → F) (g : E → F)
      (_hf : ScottContinuous f) (_hg : ScottContinuous g)
      (hfstrict : Chapter2.StrictMap f) (hgstrict : Chapter2.StrictMap g),
      ScottContinuous (mediator F f g hfstrict hgstrict)

/-- Proposition 3.2.9 support: carrier-level strict coproduct data for the
coalesced sum. -/
noncomputable def strictCoproductData :
    StrictCoproductData (D := D) (E := E) where
  inl_strict := inl_strict (D := D) (E := E)
  inr_strict := inr_strict (D := D) (E := E)
  mediator := fun _F _ _ f g _hf _hg => desc (D := D) (E := E) f g
  mediator_strict := fun _F _ _ f g _hf _hg => desc_strict (D := D) (E := E) f g
  mediator_inl := fun _F _ _ f g hf _hg x => desc_inl (D := D) (E := E) (f := f) (g := g) hf x
  mediator_inr := fun _F _ _ f g _hf hg y => desc_inr (D := D) (E := E) (f := f) (g := g) hg y
  mediator_unique := fun _F _ _ f g _hf _hg h hh hinl hinr =>
    desc_unique (D := D) (E := E) (f := f) (g := g) (h := h) hh hinl hinr

/-- Proposition 3.2.9 support: strict Scott-continuous coproduct data for
`DCPO⊥!`.  The `CONT⊥!` and `ALG⊥!` object-class closure clauses use the
continuous/algebraic domain lemmas above and are packaged with the numbered
proposition. -/
noncomputable def strictContinuousCoproductData
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    StrictContinuousCoproductData (D := D) (E := E) hDbot hEbot where
  toStrictCoproductData := strictCoproductData (D := D) (E := E)
  inl_continuous := inl_scottContinuous (D := D) (E := E) hDbot
  inr_continuous := inr_scottContinuous (D := D) (E := E) hEbot
  mediator_continuous := fun _F _ _ _f _g hf hg hfstrict hgstrict =>
    desc_scottContinuous (D := D) (E := E) hDbot hEbot hf hg hfstrict hgstrict

/-- Proposition 3.2.8: the coalesced sum of pointed dcpos is a dcpo in the
current preorder interface, with explicit hypotheses saying bottom is separated
from non-bottom elements in each summand. -/
theorem isDcpo (hD : IsDcpo D) (hE : IsDcpo E)
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) : IsDcpo (CoalescedSum D E) := by
  classical
  intro A hA
  by_cases hLeft : ∃ x : D, ∃ hx : x ≠ ⊥, inl x hx ∈ A
  · rcases hLeft with ⟨x₀, hx₀, hx₀A⟩
    have hNoRight : ∀ y : E, ∀ hy : y ≠ ⊥, inr y hy ∉ A := by
      intro y hy hyA
      rcases hA.2 hx₀A hyA with ⟨u, hu, hxle, hyle⟩
      cases u with
      | bot => exact (by simpa [CoalescedSum.le] using hxle)
      | inl x hx => exact (by simpa [CoalescedSum.le] using hyle)
      | inr y hy => exact (by simpa [CoalescedSum.le] using hxle)
    let AD : Set D := {x | x = ⊥ ∨ ∃ hx : x ≠ ⊥, inl x hx ∈ A}
    have hAD : DirectedSet AD := by
      constructor
      · exact ⟨⊥, Or.inl rfl⟩
      · intro x hx y hy
        rcases hx with rfl | ⟨hxne, hxA⟩
        · exact ⟨y, hy, bot_le, le_rfl⟩
        rcases hy with rfl | ⟨hyne, hyA⟩
        · exact ⟨x, Or.inr ⟨hxne, hxA⟩, le_rfl, bot_le⟩
        rcases hA.2 hxA hyA with ⟨u, hu, hxu, hyu⟩
        cases u with
        | bot => exact False.elim (by simpa [CoalescedSum.le] using hxu)
        | inl z hz =>
            exact ⟨z, Or.inr ⟨hz, hu⟩,
              by simpa [CoalescedSum.le] using hxu,
              by simpa [CoalescedSum.le] using hyu⟩
        | inr z hz =>
            exact False.elim (hNoRight z hz hu)
    rcases hD AD hAD with ⟨s, hs⟩
    have hs_ne : s ≠ ⊥ := by
      intro hsbot
      have hxle : x₀ ≤ ⊥ := by
        simpa [AD, hsbot] using hs.1 (Or.inr ⟨hx₀, hx₀A⟩)
      exact hx₀ (hDbot x₀ hxle)
    refine ⟨inl s hs_ne, ?_⟩
    constructor
    · intro a ha
      cases a with
      | bot => exact bot_le
      | inl x hx =>
          simpa [CoalescedSum.le] using hs.1 (Or.inr ⟨hx, ha⟩)
      | inr y hy =>
          exact False.elim (hNoRight y hy ha)
    · intro y hy
      cases y with
      | bot =>
          have hxle := hy hx₀A
          exact False.elim (by simpa [CoalescedSum.le] using hxle)
      | inl y hyne =>
          exact hs.2 y (by
            intro z hz
            rcases hz with rfl | ⟨hzne, hzA⟩
            · exact bot_le
            · simpa [CoalescedSum.le] using hy hzA)
      | inr y hyne =>
          have hxle := hy hx₀A
          exact False.elim (by simpa [CoalescedSum.le] using hxle)
  · by_cases hRight : ∃ y : E, ∃ hy : y ≠ ⊥, inr y hy ∈ A
    · rcases hRight with ⟨y₀, hy₀, hy₀A⟩
      have hNoLeft : ∀ x : D, ∀ hx : x ≠ ⊥, inl x hx ∉ A := by
        intro x hx hxA
        exact hLeft ⟨x, hx, hxA⟩
      let AE : Set E := {y | y = ⊥ ∨ ∃ hy : y ≠ ⊥, inr y hy ∈ A}
      have hAE : DirectedSet AE := by
        constructor
        · exact ⟨⊥, Or.inl rfl⟩
        · intro x hx y hy
          rcases hx with rfl | ⟨hxne, hxA⟩
          · exact ⟨y, hy, bot_le, le_rfl⟩
          rcases hy with rfl | ⟨hyne, hyA⟩
          · exact ⟨x, Or.inr ⟨hxne, hxA⟩, le_rfl, bot_le⟩
          rcases hA.2 hxA hyA with ⟨u, hu, hxu, hyu⟩
          cases u with
          | bot => exact False.elim (by simpa [CoalescedSum.le] using hxu)
          | inl z hz =>
              exact False.elim (hNoLeft z hz hu)
          | inr z hz =>
              exact ⟨z, Or.inr ⟨hz, hu⟩,
                by simpa [CoalescedSum.le] using hxu,
                by simpa [CoalescedSum.le] using hyu⟩
      rcases hE AE hAE with ⟨s, hs⟩
      have hs_ne : s ≠ ⊥ := by
        intro hsbot
        have hyle : y₀ ≤ ⊥ := by
          simpa [AE, hsbot] using hs.1 (Or.inr ⟨hy₀, hy₀A⟩)
        exact hy₀ (hEbot y₀ hyle)
      refine ⟨inr s hs_ne, ?_⟩
      constructor
      · intro a ha
        cases a with
        | bot => exact bot_le
        | inl x hx =>
            exact False.elim (hNoLeft x hx ha)
        | inr y hy =>
            simpa [CoalescedSum.le] using hs.1 (Or.inr ⟨hy, ha⟩)
      · intro y hy
        cases y with
        | bot =>
            have hyle := hy hy₀A
            exact False.elim (by simpa [CoalescedSum.le] using hyle)
        | inl x hx =>
            have hyle := hy hy₀A
            exact False.elim (by simpa [CoalescedSum.le] using hyle)
        | inr y hyne =>
            exact hs.2 y (by
              intro z hz
              rcases hz with rfl | ⟨hzne, hzA⟩
              · exact bot_le
              · simpa [CoalescedSum.le] using hy hzA)
    · refine ⟨⊥, ?_⟩
      constructor
      · intro a ha
        cases a with
        | bot => exact bot_le
        | inl x hx => exact False.elim (hLeft ⟨x, hx, ha⟩)
        | inr y hy => exact False.elim (hRight ⟨y, hy, ha⟩)
      · intro y hy
        exact bot_le

/-- Proposition 3.2.8: pointed dcpo package for coalesced sums, again with
explicit bottom-separation hypotheses for the preorder-based encoding. -/
theorem pointedDcpo (hD : IsDcpo D) (hE : IsDcpo E)
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    IsDcpo (CoalescedSum D E) ∧ Chapter2.IsLeast (⊥ : CoalescedSum D E) :=
  ⟨isDcpo (D := D) (E := E) hD hE hDbot hEbot,
    bot_isLeast (D := D) (E := E)⟩

end CoalescedSum

/-- Section 3.2.4: smash product carrier as the quotient-shaped data. -/
inductive SmashProduct where
  | bot : SmashProduct
  | pair : (x : D) → (y : E) → x ≠ ⊥ → y ≠ ⊥ → SmashProduct

namespace SmashProduct

/-- Order on the smash product: the collapsed bottom is least, and non-bottom
pairs use the componentwise product order. -/
protected def le : SmashProduct D E → SmashProduct D E → Prop
  | bot, _ => True
  | pair x y _ _, pair x' y' _ _ => x ≤ x' ∧ y ≤ y'
  | _, _ => False

instance : Preorder (SmashProduct D E) where
  le := SmashProduct.le (D := D) (E := E)
  le_refl x := by
    cases x <;> simp [SmashProduct.le]
  le_trans x y z hxy hyz := by
    cases x with
    | bot => trivial
    | pair x₁ y₁ hx₁ hy₁ =>
        cases y with
        | bot => cases hxy
        | pair x₂ y₂ hx₂ hy₂ =>
            cases z with
            | bot => cases hyz
            | pair x₃ y₃ hx₃ hy₃ =>
                exact ⟨le_trans hxy.1 hyz.1, le_trans hxy.2 hyz.2⟩

instance : OrderBot (SmashProduct D E) where
  bot := bot
  bot_le x := by
    change SmashProduct.le (D := D) (E := E) bot x
    cases x <;> simp [SmashProduct.le]

/-- Projection to the ordinary product, sending the collapsed point to the pair
of bottoms.  This is a proof device for directed suprema of the quotient-shaped
smash carrier, not a claimed inverse to `mk`. -/
def toProd : SmashProduct D E → D × E
  | bot => (⊥, ⊥)
  | pair x y _ _ => (x, y)

/-- The projection to the ordinary product is monotone for the smash-product
order. -/
theorem toProd_monotone : Monotone (toProd (D := D) (E := E)) := by
  intro x y hxy
  cases x with
  | bot =>
      cases y with
      | bot => exact ⟨le_rfl, le_rfl⟩
      | pair x y hx hy => exact ⟨bot_le, bot_le⟩
  | pair x₁ y₁ hx₁ hy₁ =>
      cases y with
      | bot => cases hxy
      | pair x₂ y₂ hx₂ hy₂ => exact hxy

/-- Smash-product introduction map: any pair with a bottom coordinate is sent to
the collapsed bottom; otherwise the non-bottom pair is remembered. -/
noncomputable def mk (x : D) (y : E) : SmashProduct D E := by
  classical
  exact if hx : x = ⊥ then bot else if hy : y = ⊥ then bot else pair x y hx hy

@[simp] theorem mk_bot_left (y : E) :
    mk (D := D) (E := E) ⊥ y = (⊥ : SmashProduct D E) := by
  change mk (D := D) (E := E) ⊥ y = bot
  simp [mk]

@[simp] theorem mk_bot_right (x : D) :
    mk (D := D) (E := E) x ⊥ = (⊥ : SmashProduct D E) := by
  classical
  change mk (D := D) (E := E) x ⊥ = bot
  by_cases hx : x = ⊥
  · simp [mk, hx]
  · simp [mk, hx]

theorem mk_of_ne {x : D} {y : E} (hx : x ≠ ⊥) (hy : y ≠ ⊥) :
    mk (D := D) (E := E) x y = pair x y hx hy := by
  simp [mk, hx, hy]

/-- `mk` reconstitutes every smash-product element after projection to the
ordinary product. -/
theorem mk_toProd (z : SmashProduct D E) :
    mk (D := D) (E := E) (toProd (D := D) (E := E) z).1
      (toProd (D := D) (E := E) z).2 = z := by
  cases z with
  | bot =>
      change mk (D := D) (E := E) (⊥ : D) (⊥ : E) = (⊥ : SmashProduct D E)
      exact mk_bot_left (D := D) (E := E) ⊥
  | pair x y hx hy =>
      simp [toProd, mk_of_ne (D := D) (E := E) hx hy]

/-- Mapping a set of smash-product elements to the ordinary product and back
with `mk` recovers the original set. -/
theorem mk_image_toProd_eq (A : Set (SmashProduct D E)) :
    ((fun p : D × E => mk (D := D) (E := E) p.1 p.2) ''
        (toProd (D := D) (E := E) '' A)) = A := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨p, ⟨a, ha, rfl⟩, hpz⟩
    have hpz' : a = z := by
      simpa [mk_toProd (D := D) (E := E) a] using hpz
    simpa [← hpz'] using ha
  · intro hz
    exact ⟨toProd (D := D) (E := E) z, ⟨z, hz, rfl⟩,
      mk_toProd (D := D) (E := E) z⟩

/-- The collapsed point is least in the smash product. -/
theorem bot_isLeast : Chapter2.IsLeast (⊥ : SmashProduct D E) := by
  intro x
  exact bot_le

/-- Nothing except the collapsed point is below the collapsed point. -/
theorem eq_bot_of_le_bot {x : SmashProduct D E} (hx : x ≤ ⊥) :
    x = (⊥ : SmashProduct D E) := by
  cases x with
  | bot => rfl
  | pair x y hxne hyne =>
      exact False.elim (by simpa [SmashProduct.le] using hx)

/-- The smash product inherits antisymmetry from its two coordinates.  This is
the partial-order side condition for the later pointed-dcpo object package. -/
theorem antisymmetric_of_components
    (hDanti : ∀ x y : D, x ≤ y → y ≤ x → x = y)
    (hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y) :
    ∀ x y : SmashProduct D E, x ≤ y → y ≤ x → x = y := by
  intro x y hxy hyx
  cases x with
  | bot =>
      exact (eq_bot_of_le_bot (D := D) (E := E) hyx).symm
  | pair x₁ y₁ hx₁ hy₁ =>
      cases y with
      | bot =>
          exact eq_bot_of_le_bot (D := D) (E := E) hxy
      | pair x₂ y₂ hx₂ hy₂ =>
          have hx_eq : x₁ = x₂ := hDanti x₁ x₂ hxy.1 hyx.1
          have hy_eq : y₁ = y₂ := hEanti y₁ y₂ hxy.2 hyx.2
          subst x₂
          subst y₂
          simp

/-- The smash-product introduction map is strict in the left coordinate. -/
theorem mk_left_strict (y : E) :
    Chapter2.StrictMap (fun x : D => mk (D := D) (E := E) x y) :=
  mk_bot_left (D := D) (E := E) y

/-- The smash-product introduction map is strict in the right coordinate. -/
theorem mk_right_strict (x : D) :
    Chapter2.StrictMap (fun y : E => mk (D := D) (E := E) x y) :=
  mk_bot_right (D := D) (E := E) x

/-- The smash-product introduction map is monotone in the product order.  The
explicit bottom-separation assumptions compensate for the local preorder-based
interface; in a bundled poset they follow from antisymmetry. -/
theorem mk_monotone
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    Monotone (fun p : D × E => mk (D := D) (E := E) p.1 p.2) := by
  classical
  intro p q hpq
  rcases p with ⟨x, y⟩
  rcases q with ⟨x', y'⟩
  rcases hpq with ⟨hxx', hyy'⟩
  by_cases hx : x = ⊥
  · subst x
    change mk (D := D) (E := E) ⊥ y ≤ mk (D := D) (E := E) x' y'
    rw [mk_bot_left (D := D) (E := E)]
    exact bot_le
  · by_cases hy : y = ⊥
    · subst y
      change mk (D := D) (E := E) x ⊥ ≤ mk (D := D) (E := E) x' y'
      rw [mk_bot_right (D := D) (E := E)]
      exact bot_le
    · have hx' : x' ≠ ⊥ := by
        intro hx'bot
        exact hx (hDbot x (by simpa [hx'bot] using hxx'))
      have hy' : y' ≠ ⊥ := by
        intro hy'bot
        exact hy (hEbot y (by simpa [hy'bot] using hyy'))
      have hxx : x ≤ x' := by simpa using hxx'
      have hyy : y ≤ y' := by simpa using hyy'
      change mk (D := D) (E := E) x y ≤ mk (D := D) (E := E) x' y'
      rw [mk_of_ne (D := D) (E := E) hx hy,
        mk_of_ne (D := D) (E := E) hx' hy']
      exact ⟨hxx, hyy⟩

/-- The smash-product introduction map preserves existing directed suprema.
This is the continuity half of the tensor carrier support; the explicit
bottom-separation hypotheses again stand in for antisymmetry of pointed posets
in the local preorder-based interface. -/
theorem mk_preserves_directed_sup
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    {A : Set (D × E)} {s : D × E}
    (hA : DirectedSet A) (hs : IsSup A s) :
    IsSup ((fun p : D × E => mk (D := D) (E := E) p.1 p.2) '' A)
      (mk (D := D) (E := E) s.1 s.2) := by
  classical
  constructor
  · intro z hz
    rcases hz with ⟨a, ha, rfl⟩
    exact mk_monotone (D := D) (E := E) hDbot hEbot (hs.1 ha)
  · intro z hz
    by_cases hsx : s.1 = ⊥
    · rw [show mk (D := D) (E := E) s.1 s.2 = (⊥ : SmashProduct D E) by
        simpa [hsx] using mk_bot_left (D := D) (E := E) s.2]
      exact bot_le
    · by_cases hsy : s.2 = ⊥
      · rw [show mk (D := D) (E := E) s.1 s.2 = (⊥ : SmashProduct D E) by
          simpa [hsy] using mk_bot_right (D := D) (E := E) s.1]
        exact bot_le
      · have hleftExists : ∃ a : D × E, a ∈ A ∧ a.1 ≠ ⊥ := by
          by_contra hnone
          have hbotUpper : IsUpperBound A ((⊥ : D), s.2) := by
            intro a ha
            constructor
            · have ha_bot : a.1 = ⊥ := by
                by_contra hane
                exact hnone ⟨a, ha, hane⟩
              simpa [ha_bot]
            · exact (hs.1 ha).2
          have hs_le : s ≤ ((⊥ : D), s.2) := hs.2 ((⊥ : D), s.2) hbotUpper
          exact hsx (hDbot s.1 (by simpa using hs_le.1))
        have hrightExists : ∃ a : D × E, a ∈ A ∧ a.2 ≠ ⊥ := by
          by_contra hnone
          have hbotUpper : IsUpperBound A (s.1, (⊥ : E)) := by
            intro a ha
            constructor
            · exact (hs.1 ha).1
            · have ha_bot : a.2 = ⊥ := by
                by_contra hane
                exact hnone ⟨a, ha, hane⟩
              simpa [ha_bot]
          have hs_le : s ≤ (s.1, (⊥ : E)) := hs.2 (s.1, (⊥ : E)) hbotUpper
          exact hsy (hEbot s.2 (by simpa using hs_le.2))
        rcases hleftExists with ⟨aL, haL, haLne⟩
        rcases hrightExists with ⟨aR, haR, haRne⟩
        rw [mk_of_ne (D := D) (E := E) hsx hsy]
        cases z with
        | bot =>
            rcases hA.2 haL haR with ⟨c, hc, haLc, haRc⟩
            have hcLeft : c.1 ≠ ⊥ := by
              intro hcbot
              exact haLne (hDbot aL.1 (by simpa [hcbot] using haLc.1))
            have hcRight : c.2 ≠ ⊥ := by
              intro hcbot
              exact haRne (hEbot aR.2 (by simpa [hcbot] using haRc.2))
            have hle : mk (D := D) (E := E) c.1 c.2 ≤ (⊥ : SmashProduct D E) :=
              hz ⟨c, hc, rfl⟩
            exact False.elim (by
              simpa [mk_of_ne (D := D) (E := E) hcLeft hcRight, SmashProduct.le]
                using hle)
        | pair u v hu hv =>
            have hUpperA : IsUpperBound A (u, v) := by
              intro a ha
              constructor
              · by_cases haLeft : a.1 = ⊥
                · simpa [haLeft]
                · rcases hA.2 ha haR with ⟨c, hc, hac, haRc⟩
                  have hcLeft : c.1 ≠ ⊥ := by
                    intro hcbot
                    exact haLeft (hDbot a.1 (by simpa [hcbot] using hac.1))
                  have hcRight : c.2 ≠ ⊥ := by
                    intro hcbot
                    exact haRne (hEbot aR.2 (by simpa [hcbot] using haRc.2))
                  have hle : mk (D := D) (E := E) c.1 c.2 ≤ pair u v hu hv :=
                    hz ⟨c, hc, rfl⟩
                  have hpair_le : pair c.1 c.2 hcLeft hcRight ≤ pair u v hu hv := by
                    simpa [mk_of_ne (D := D) (E := E) hcLeft hcRight,
                      SmashProduct.le] using hle
                  have hc_le : c.1 ≤ u := hpair_le.1
                  exact le_trans hac.1 hc_le
              · by_cases haRight : a.2 = ⊥
                · simpa [haRight]
                · rcases hA.2 haL ha with ⟨c, hc, haLc, hac⟩
                  have hcLeft : c.1 ≠ ⊥ := by
                    intro hcbot
                    exact haLne (hDbot aL.1 (by simpa [hcbot] using haLc.1))
                  have hcRight : c.2 ≠ ⊥ := by
                    intro hcbot
                    exact haRight (hEbot a.2 (by simpa [hcbot] using hac.2))
                  have hle : mk (D := D) (E := E) c.1 c.2 ≤ pair u v hu hv :=
                    hz ⟨c, hc, rfl⟩
                  have hpair_le : pair c.1 c.2 hcLeft hcRight ≤ pair u v hu hv := by
                    simpa [mk_of_ne (D := D) (E := E) hcLeft hcRight,
                      SmashProduct.le] using hle
                  have hc_le : c.2 ≤ v := hpair_le.2
                  exact le_trans hac.2 hc_le
            exact hs.2 (u, v) hUpperA

/-- The smash-product introduction map is Scott-continuous. -/
theorem mk_scottContinuous
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    ScottContinuous (fun p : D × E => mk (D := D) (E := E) p.1 p.2) :=
  ⟨mk_monotone (D := D) (E := E) hDbot hEbot,
    fun {_A} {_x} hA hs =>
      mk_preserves_directed_sup (D := D) (E := E) hDbot hEbot hA hs⟩

/-- Projecting after introducing into the smash product is below the original
ordinary-product point.  Equality can fail when a coordinate is bottom, because
`mk` collapses that point to the smash bottom. -/
theorem toProd_mk_le (x : D) (y : E) :
    toProd (D := D) (E := E) (mk (D := D) (E := E) x y) ≤ (x, y) := by
  classical
  by_cases hx : x = ⊥
  · subst x
    rw [mk_bot_left (D := D) (E := E)]
    exact ⟨le_rfl, bot_le⟩
  · by_cases hy : y = ⊥
    · subst y
      rw [mk_bot_right (D := D) (E := E)]
      exact ⟨bot_le, le_rfl⟩
    · rw [mk_of_ne (D := D) (E := E) hx hy]
      exact ⟨le_rfl, le_rfl⟩

/-- The projection to the ordinary product preserves existing directed
suprema.  This is the quotient-shaped companion to `mk_preserves_directed_sup`.
-/
theorem toProd_preserves_directed_sup
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    {A : Set (SmashProduct D E)} {s : SmashProduct D E}
    (_hA : DirectedSet A) (hs : IsSup A s) :
    IsSup (toProd (D := D) (E := E) '' A) (toProd (D := D) (E := E) s) := by
  constructor
  · intro p hp
    rcases hp with ⟨a, ha, rfl⟩
    exact toProd_monotone (D := D) (E := E) (hs.1 ha)
  · intro q hq
    have hmkUpper : IsUpperBound A (mk (D := D) (E := E) q.1 q.2) := by
      intro a ha
      have hto : toProd (D := D) (E := E) a ≤ q := hq ⟨a, ha, rfl⟩
      have hmk :
          mk (D := D) (E := E) (toProd (D := D) (E := E) a).1
              (toProd (D := D) (E := E) a).2 ≤
            mk (D := D) (E := E) q.1 q.2 :=
        mk_monotone (D := D) (E := E) hDbot hEbot hto
      simpa [mk_toProd (D := D) (E := E) a] using hmk
    exact le_trans (toProd_monotone (D := D) (E := E) (hs.2 _ hmkUpper))
      (toProd_mk_le (D := D) (E := E) q.1 q.2)

/-- The projection from the smash product to the ordinary product is
Scott-continuous. -/
theorem toProd_scottContinuous
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    ScottContinuous (toProd (D := D) (E := E)) :=
  ⟨toProd_monotone (D := D) (E := E),
    fun {_A} {_s} hA hs =>
      toProd_preserves_directed_sup (D := D) (E := E) hDbot hEbot hA hs⟩

/-- The left-variable section of the smash-product introduction map is
Scott-continuous. -/
theorem mk_left_section_scottContinuous
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) (y : E) :
    ScottContinuous (fun x : D => mk (D := D) (E := E) x y) := by
  have hpair : ScottContinuous (fun x : D => (x, y)) :=
    prod_pair_scottContinuous scottContinuous_id (const_scottContinuous y)
  have hcomp := ScottContinuous.comp
    (f := fun p : D × E => mk (D := D) (E := E) p.1 p.2)
    (g := fun x : D => (x, y))
    (mk_scottContinuous (D := D) (E := E) hDbot hEbot) hpair
  simpa using hcomp

/-- The right-variable section of the smash-product introduction map is
Scott-continuous. -/
theorem mk_right_section_scottContinuous
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) (x : D) :
    ScottContinuous (fun y : E => mk (D := D) (E := E) x y) := by
  have hpair : ScottContinuous (fun y : E => (x, y)) :=
    prod_pair_scottContinuous (const_scottContinuous x) scottContinuous_id
  have hcomp := ScottContinuous.comp
    (f := fun p : D × E => mk (D := D) (E := E) p.1 p.2)
    (g := fun y : E => (x, y))
    (mk_scottContinuous (D := D) (E := E) hDbot hEbot) hpair
  simpa using hcomp

/-- The smash product of pointed dcpos is a dcpo.  Directed suprema are
computed by projecting to the ordinary product dcpo and then applying `mk`.
The bottom-separation hypotheses are the preorder-interface replacement for
antisymmetry of pointed posets. -/
theorem isDcpo (hD : IsDcpo D) (hE : IsDcpo E)
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    IsDcpo (SmashProduct D E) := by
  intro A hA
  let P : Set (D × E) := toProd (D := D) (E := E) '' A
  have hP : DirectedSet P :=
    DirectedSet.image (f := toProd (D := D) (E := E))
      (toProd_monotone (D := D) (E := E)) hA
  rcases prod_isDcpo (D := D) (E := E) hD hE P hP with ⟨s, hs⟩
  refine ⟨mk (D := D) (E := E) s.1 s.2, ?_⟩
  have hmkSup :
      IsSup ((fun p : D × E => mk (D := D) (E := E) p.1 p.2) '' P)
        (mk (D := D) (E := E) s.1 s.2) :=
    mk_preserves_directed_sup (D := D) (E := E) hDbot hEbot hP hs
  change
    IsSup ((fun p : D × E => mk (D := D) (E := E) p.1 p.2) ''
        (toProd (D := D) (E := E) '' A))
      (mk (D := D) (E := E) s.1 s.2) at hmkSup
  simpa [mk_image_toProd_eq (D := D) (E := E) A] using hmkSup

/-- Pointed dcpo package for the smash product carrier. -/
theorem pointedDcpo (hD : IsDcpo D) (hE : IsDcpo E)
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    IsDcpo (SmashProduct D E) ∧ Chapter2.IsLeast (⊥ : SmashProduct D E) :=
  ⟨isDcpo (D := D) (E := E) hD hE hDbot hEbot,
    bot_isLeast (D := D) (E := E)⟩

end SmashProduct

/-- Section 3.2.5: lifting, implemented by Mathlib's `WithBot`. -/
abbrev Lifting (D : Type u) := WithBot D

/-- The canonical map `up : D → D⊥`. -/
def up (x : D) : Lifting D := some x

end SumsSmashLifting

end Chapter3
end AbramskyJung

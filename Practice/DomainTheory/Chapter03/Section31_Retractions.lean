import Practice.DomainTheory.Chapter03.Prelude

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 3.1: retractions and idempotents

This file is one split component of Chapter 3.  It imports the Chapter 3
prelude, whose order-theoretic vocabulary is aliased to Chapter 2.
-/

universe u v

namespace AbramskyJung
namespace Chapter3

section Retractions

variable {P : Type u} [Preorder P]
variable {Q : Type v} [Preorder Q]

/-- Definition 3.1.1: monotone section-retraction pairs. -/
structure SectionRetractionPair (P : Type u) (Q : Type v) [Preorder P] [Preorder Q] where
  s : P → Q
  r : Q → P
  monotone_s : Monotone s
  monotone_r : Monotone r
  retract : ∀ x : P, r (s x) = x

namespace SectionRetractionPair

variable (sr : SectionRetractionPair P Q)

/-- In an s-r-pair, the retraction is surjective. -/
theorem retraction_surjective : Function.Surjective sr.r := by
  intro x
  exact ⟨sr.s x, sr.retract x⟩

/-- In an s-r-pair, the section is injective. -/
theorem section_injective : Function.Injective sr.s := by
  intro x y hxy
  have h := congrArg sr.r hxy
  simpa [sr.retract x, sr.retract y] using h

/-- Proposition 3.1.2(1), supremum part. -/
theorem isSup_of_section_image_isSup {A : Set P} {q : Q}
    (hq : IsSup (sr.s '' A) q) : IsSup A (sr.r q) := by
  constructor
  · intro a ha
    calc
      a = sr.r (sr.s a) := (sr.retract a).symm
      _ ≤ sr.r q := sr.monotone_r (hq.1 ⟨a, ha, rfl⟩)
  · intro y hy
    have hsy : IsUpperBound (sr.s '' A) (sr.s y) := by
      intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact sr.monotone_s (hy ha)
    calc
      sr.r q ≤ sr.r (sr.s y) := sr.monotone_r (hq.2 (sr.s y) hsy)
      _ = y := sr.retract y

/-- Proposition 3.1.2(1), infimum part. -/
theorem isInf_of_section_image_isInf {A : Set P} {q : Q}
    (hq : IsInf (sr.s '' A) q) : IsInf A (sr.r q) := by
  constructor
  · intro a ha
    calc
      sr.r q ≤ sr.r (sr.s a) := sr.monotone_r (hq.1 ⟨a, ha, rfl⟩)
      _ = a := sr.retract a
  · intro y hy
    have hsy : IsLowerBound (sr.s '' A) (sr.s y) := by
      intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact sr.monotone_s (hy ha)
    calc
      y = sr.r (sr.s y) := (sr.retract y).symm
      _ ≤ sr.r q := sr.monotone_r (hq.2 (sr.s y) hsy)

/-- Proposition 3.1.2(2), dcpo part: monotone retracts inherit dcpos. -/
theorem isDcpo_of_isDcpo (sr : SectionRetractionPair P Q)
    (hQ : IsDcpo Q) : IsDcpo P := by
  intro A hA
  have hImageDirected : DirectedSet (sr.s '' A) :=
    DirectedSet.image sr.monotone_s hA
  rcases hQ (sr.s '' A) hImageDirected with ⟨q, hq⟩
  exact ⟨sr.r q, sr.isSup_of_section_image_isSup hq⟩

/-- The bottom of a pointed codomain retracts to a bottom element. -/
theorem isLeast_retracted_bot [OrderBot Q] : Chapter2.IsLeast (sr.r ⊥) := by
  intro x
  calc
    sr.r ⊥ ≤ sr.r (sr.s x) := sr.monotone_r bot_le
    _ = x := sr.retract x

/-- A pointed codomain induces an `OrderBot` structure on the retract. -/
@[reducible]
def orderBotOfOrderBot [OrderBot Q] : OrderBot P where
  bot := sr.r ⊥
  bot_le := sr.isLeast_retracted_bot

/-- Proposition 3.1.2(2), pointed-dcpo part.  Pointedness is recorded by the
explicit least element because this file avoids installing local typeclass
instances for arbitrary retractions. -/
theorem pointedDcpo_of_pointedDcpo [OrderBot Q] (hQ : IsDcpo Q) :
    IsDcpo P ∧ Chapter2.IsLeast (sr.r ⊥) :=
  ⟨sr.isDcpo_of_isDcpo hQ, sr.isLeast_retracted_bot⟩

/-- Proposition 3.1.2(2), join-semilattice part. -/
theorem hasBinaryJoins_of_hasBinaryJoins
    (sr : SectionRetractionPair P Q)
    (hQ : Chapter2.HasBinaryJoins Q) : Chapter2.HasBinaryJoins P := by
  intro x y
  let A : Set P := {w | w = x ∨ w = y}
  rcases hQ (sr.s x) (sr.s y) with ⟨q, hq⟩
  have hImage :
      sr.s '' A = ({z | z = sr.s x ∨ z = sr.s y} : Set Q) := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨w, hw, rfl⟩
      rcases hw with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro hz
      rcases hz with rfl | rfl
      · exact ⟨x, Or.inl rfl, rfl⟩
      · exact ⟨y, Or.inr rfl, rfl⟩
  exact ⟨sr.r q, sr.isSup_of_section_image_isSup (by simpa [A, hImage] using hq)⟩

/-- Proposition 3.1.2(2), meet-semilattice part. -/
theorem hasBinaryMeets_of_hasBinaryMeets
    (sr : SectionRetractionPair P Q)
    (hQ : Chapter2.HasBinaryMeets Q) : Chapter2.HasBinaryMeets P := by
  intro x y
  let A : Set P := {w | w = x ∨ w = y}
  rcases hQ (sr.s x) (sr.s y) with ⟨q, hq⟩
  have hImage :
      sr.s '' A = ({z | z = sr.s x ∨ z = sr.s y} : Set Q) := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨w, hw, rfl⟩
      rcases hw with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro hz
      rcases hz with rfl | rfl
      · exact ⟨x, Or.inl rfl, rfl⟩
      · exact ⟨y, Or.inr rfl, rfl⟩
  exact ⟨sr.r q, sr.isInf_of_section_image_isInf (by simpa [A, hImage] using hq)⟩

/-- Proposition 3.1.2(2), lattice part. -/
theorem isLatticeOrder_of_isLatticeOrder
    (sr : SectionRetractionPair P Q)
    (hQ : Chapter2.IsLatticeOrder Q) : Chapter2.IsLatticeOrder P :=
  ⟨sr.hasBinaryJoins_of_hasBinaryJoins hQ.1,
    sr.hasBinaryMeets_of_hasBinaryMeets hQ.2⟩

/-- Proposition 3.1.2(2), complete-lattice part in the predicate-level
`IsCompleteOrder` interface from Chapter 2. -/
theorem isCompleteOrder_of_isCompleteOrder
    (sr : SectionRetractionPair P Q)
    (hQ : Chapter2.IsCompleteOrder Q) : Chapter2.IsCompleteOrder P := by
  constructor
  · intro A
    rcases hQ.1 (sr.s '' A) with ⟨q, hq⟩
    exact ⟨sr.r q, sr.isSup_of_section_image_isSup hq⟩
  · intro A
    rcases hQ.2 (sr.s '' A) with ⟨q, hq⟩
    exact ⟨sr.r q, sr.isInf_of_section_image_isInf hq⟩

end SectionRetractionPair

/-- Definition 3.1.1: continuous section-retraction pairs between dcpo-like posets. -/
structure ContinuousSectionRetractionPair
    (D : Type u) (E : Type v) [Preorder D] [Preorder E]
    extends SectionRetractionPair D E where
  continuous_s : ScottContinuous s
  continuous_r : ScottContinuous r

end Retractions

section Idempotents

variable {D : Type u} [Preorder D]

/-- Continuous idempotent self-maps, Section 3.1.2. -/
structure ContinuousIdempotent (D : Type u) [Preorder D] where
  f : D → D
  continuous : ScottContinuous f
  idem : ∀ x : D, f (f x) = f x

namespace ContinuousIdempotent

variable (e : ContinuousIdempotent D)

/-- The image of an idempotent is the set of its fixed points. -/
theorem mem_range_iff_fixed {y : D} : y ∈ Set.range e.f ↔ e.f y = y := by
  constructor
  · intro hy
    rcases hy with ⟨x, rfl⟩
    exact e.idem x
  · intro hy
    exact ⟨y, hy⟩

/-- The image carrier of a continuous idempotent. -/
def ImageCarrier : Type u :=
  {x : D // x ∈ Set.range e.f}

instance imageCarrierPreorder : Preorder e.ImageCarrier where
  le x y := x.1 ≤ y.1
  le_refl x := le_rfl
  le_trans x y z hxy hyz := le_trans hxy hyz

/-- The inclusion of the idempotent image into the ambient carrier. -/
def inclusion : e.ImageCarrier → D :=
  fun x => x.1

/-- The idempotent map, corestricted to its image. -/
def projection (x : D) : e.ImageCarrier :=
  ⟨e.f x, ⟨x, rfl⟩⟩

/-- The inclusion is monotone. -/
theorem inclusion_monotone : Monotone e.inclusion := by
  intro x y hxy
  exact hxy

/-- The projection is monotone. -/
theorem projection_monotone : Monotone e.projection := by
  intro x y hxy
  exact e.continuous.1 hxy

/-- Projecting a point already in the image returns it. -/
theorem projection_inclusion_eq (x : e.ImageCarrier) :
    e.projection (e.inclusion x) = x := by
  apply Subtype.ext
  exact (e.mem_range_iff_fixed).1 x.2

/-- Inclusion after projection is the original idempotent. -/
theorem inclusion_projection_eq (x : D) :
    e.inclusion (e.projection x) = e.f x := rfl

/-- The image of a continuous idempotent is a monotone retract of the ambient
carrier. -/
def sectionRetractionPair : SectionRetractionPair e.ImageCarrier D where
  s := e.inclusion
  r := e.projection
  monotone_s := e.inclusion_monotone
  monotone_r := e.projection_monotone
  retract := e.projection_inclusion_eq

/-- The projection onto an idempotent image is Scott-continuous. -/
theorem projection_scottContinuous : ScottContinuous e.projection := by
  constructor
  · exact e.projection_monotone
  · intro A s hA hs
    have hfsup : IsSup (e.f '' A) (e.f s) := e.continuous.2 hA hs
    constructor
    · intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      exact hfsup.1 ⟨a, ha, rfl⟩
    · intro y hy
      exact hfsup.2 y.1 (by
        intro z hz
        rcases hz with ⟨a, ha, rfl⟩
        exact hy ⟨a, ha, rfl⟩)

end ContinuousIdempotent

variable {Dpo : Type u} [PartialOrder Dpo]

/-- Proposition 3.1.7(1), support: a directed supremum of fixed points is fixed. -/
theorem continuous_idempotent_sup_of_image_mem
    (e : ContinuousIdempotent Dpo) {A : Set Dpo} {s : Dpo}
    (hA : DirectedSet A) (hsub : A ⊆ Set.range e.f) (hs : IsSup A s) :
    s ∈ Set.range e.f := by
  have hfixedA : ∀ a ∈ A, e.f a = a := by
    intro a ha
    exact (e.mem_range_iff_fixed).1 (hsub ha)
  have himage_eq : e.f '' A = A := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨a, ha, rfl⟩
      simpa [hfixedA a ha] using ha
    · intro hz
      exact ⟨z, hz, hfixedA z hz⟩
  have hfsup : IsSup (e.f '' A) (e.f s) := e.continuous.2 hA hs
  have hfsupA : IsSup A (e.f s) := by
    simpa [himage_eq] using hfsup
  have hEq : e.f s = s := IsSup.unique hfsupA hs
  exact ⟨s, hEq⟩

namespace ContinuousIdempotent

variable (e : ContinuousIdempotent Dpo)

/-- Proposition 3.1.7(1): the image of a continuous idempotent on a dcpo is a
dcpo. -/
theorem image_isDcpo (hD : IsDcpo Dpo) : IsDcpo e.ImageCarrier := by
  intro A hA
  have hImageDirected : DirectedSet (e.inclusion '' A) :=
    DirectedSet.image e.inclusion_monotone hA
  rcases hD (e.inclusion '' A) hImageDirected with ⟨s, hs⟩
  have hsub : e.inclusion '' A ⊆ Set.range e.f := by
    intro y hy
    rcases hy with ⟨a, _ha, rfl⟩
    exact a.2
  have hsMem : s ∈ Set.range e.f :=
    continuous_idempotent_sup_of_image_mem e hImageDirected hsub hs
  refine ⟨⟨s, hsMem⟩, ?_⟩
  constructor
  · intro a ha
    exact hs.1 ⟨a, ha, rfl⟩
  · intro y hy
    exact hs.2 y.1 (by
      intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact hy ha)

/-- Proposition 3.1.7(1): directed suprema in the image coincide with ambient
directed suprema. -/
theorem image_isSup_iff_ambient_isSup
    (hD : IsDcpo Dpo) {A : Set e.ImageCarrier} {s : e.ImageCarrier}
    (hA : DirectedSet A) :
    IsSup A s ↔ IsSup (e.inclusion '' A) (e.inclusion s) := by
  constructor
  · intro hs
    have hImageDirected : DirectedSet (e.inclusion '' A) :=
      DirectedSet.image e.inclusion_monotone hA
    rcases hD (e.inclusion '' A) hImageDirected with ⟨t, ht⟩
    have hsub : e.inclusion '' A ⊆ Set.range e.f := by
      intro y hy
      rcases hy with ⟨a, _ha, rfl⟩
      exact a.2
    have htMem : t ∈ Set.range e.f :=
      continuous_idempotent_sup_of_image_mem e hImageDirected hsub ht
    let tImage : e.ImageCarrier := ⟨t, htMem⟩
    constructor
    · intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      exact hs.1 ha
    · intro y hy
      have hs_le_t : s ≤ tImage := hs.2 tImage (by
        intro a ha
        exact ht.1 ⟨a, ha, rfl⟩)
      exact le_trans hs_le_t (ht.2 y hy)
  · intro hs
    constructor
    · intro a ha
      exact hs.1 ⟨a, ha, rfl⟩
    · intro y hy
      exact hs.2 y.1 (by
        intro z hz
        rcases hz with ⟨a, ha, rfl⟩
        exact hy ha)

/-- Proposition 3.1.7(1): the inclusion of the image into the ambient dcpo is
Scott-continuous. -/
theorem inclusion_scottContinuous (hD : IsDcpo Dpo) :
    ScottContinuous e.inclusion := by
  constructor
  · exact e.inclusion_monotone
  · intro A s hA hs
    exact (e.image_isSup_iff_ambient_isSup hD hA).1 hs

/-- The idempotent image and the ambient dcpo form a continuous
section-retraction pair. -/
def continuousSectionRetractionPair (hD : IsDcpo Dpo) :
    ContinuousSectionRetractionPair e.ImageCarrier Dpo where
  toSectionRetractionPair := e.sectionRetractionPair
  continuous_s := e.inclusion_scottContinuous hD
  continuous_r := e.projection_scottContinuous

/-- A continuous idempotent as a bundled Scott-continuous self-map. -/
def toScottContFun : Chapter2.ScottContFun Dpo Dpo :=
  { toFun := e.f, continuous := e.continuous }

end ContinuousIdempotent

instance continuousIdempotentPreorder : Preorder (ContinuousIdempotent Dpo) where
  le e g := ∀ x : Dpo, e.f x ≤ g.f x
  le_refl e x := le_rfl
  le_trans e g h heg hgh x := le_trans (heg x) (hgh x)

/-- Proposition 3.1.7(2): continuous idempotent self-maps on a dcpo form a
dcpo. -/
theorem continuousIdempotent_isDcpo (hD : IsDcpo Dpo) :
    IsDcpo (ContinuousIdempotent Dpo) := by
  classical
  intro F hF
  let G : Set (Chapter2.ScottContFun Dpo Dpo) :=
    ContinuousIdempotent.toScottContFun '' F
  have hG : DirectedSet G := by
    constructor
    · rcases hF.1 with ⟨e, he⟩
      exact ⟨e.toScottContFun, ⟨e, he, rfl⟩⟩
    · intro f hf g hg
      rcases hf with ⟨e, he, rfl⟩
      rcases hg with ⟨d, hd, rfl⟩
      rcases hF.2 he hd with ⟨m, hm, hem, hdm⟩
      exact ⟨m.toScottContFun, ⟨m, hm, rfl⟩, hem, hdm⟩
  rcases Chapter2.prop_2_1_18_continuous_function_space_dcpo hD G hG with ⟨g, hg⟩
  have evalSup : ∀ x : Dpo,
      IsSup ((fun f : Chapter2.ScottContFun Dpo Dpo => f x) '' G) (g x) := by
    intro x
    exact Chapter2.scottContFun_directed_sup_apply hD hG hg x
  have hgIdem : ∀ x : Dpo, g (g x) = g x := by
    intro x
    apply le_antisymm
    · have hEvalSupX := evalSup x
      have hEvalSupGX := evalSup (g x)
      refine hEvalSupGX.2 (g x) ?_
      intro y hy
      rcases hy with ⟨f, hf, rfl⟩
      rcases hf with ⟨e, he, rfl⟩
      have hcontSup : IsSup (e.f '' ((fun f : Chapter2.ScottContFun Dpo Dpo => f x) '' G))
          (e.f (g x)) :=
        e.continuous.2 (DirectedSet.image (by
          intro f g hfg
          exact hfg x) hG) hEvalSupX
      refine hcontSup.2 (g x) ?_
      intro z hz
      rcases hz with ⟨fx, hfx, rfl⟩
      rcases hfx with ⟨f', hf', rfl⟩
      rcases hf' with ⟨d, hd, rfl⟩
      rcases hF.2 he hd with ⟨m, hm, hem, hdm⟩
      calc
        e.f (d.f x) ≤ m.f (d.f x) := hem (d.f x)
        _ ≤ m.f (m.f x) := m.continuous.1 (hdm x)
        _ = m.f x := m.idem x
        _ ≤ g x := hg.1 ⟨m, hm, rfl⟩ x
    · have hEvalSupX := evalSup x
      have hEvalSupGX := evalSup (g x)
      refine hEvalSupX.2 (g (g x)) ?_
      intro y hy
      rcases hy with ⟨f, hf, rfl⟩
      rcases hf with ⟨e, he, rfl⟩
      have hex_le_gx : e.f x ≤ g x := hg.1 ⟨e, he, rfl⟩ x
      have hex_le_egx : e.f x ≤ e.f (g x) := by
        calc
          e.f x = e.f (e.f x) := (e.idem x).symm
          _ ≤ e.f (g x) := e.continuous.1 hex_le_gx
      have heg_le_ggx : e.f (g x) ≤ g (g x) := hg.1 ⟨e, he, rfl⟩ (g x)
      exact le_trans hex_le_egx heg_le_ggx
  let esup : ContinuousIdempotent Dpo :=
    { f := g
      continuous := g.continuous
      idem := hgIdem }
  refine ⟨esup, ?_⟩
  constructor
  · intro e he x
    exact hg.1 ⟨e, he, rfl⟩ x
  · intro e he x
    exact hg.2 e.toScottContFun (by
      intro f hf
      rcases hf with ⟨d, hd, rfl⟩
      exact he hd) x

end Idempotents

end Chapter3
end AbramskyJung

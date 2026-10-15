import Practice.DomainTheory.Chapter03.NumberedItems.Section33_BilimitConstruction

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Chapter 3: Section 3.3 bilimit universal properties

Book-facing declarations and their local support API are kept together in
textbook dependency order. Reusable constructions remain in the concept-owned
`Chapter03.Section*` modules.
-/

universe u v w z l

namespace AbramskyJung
namespace Chapter3

/-- The statement form of Proposition 3.3.9.

PDF text: "Let `⟨E,(f_n)_{n∈N}⟩` be a cocone over the expanding sequence
`⟨(D_n)_{n∈N}, (e_mn : D_n → D_m)_{n≤m∈N}⟩` where the `f_n` are embeddings.
Then the bilimit of the sequence is a sub-domain of `E`."

Current Lean spelling: in the preorder interface, stage dcpo and stage
antisymmetry hypotheses are explicit, the target cocone carrier is required to
be a dcpo, and the embedding assumption on the cocone legs is supplied as
`CoconeEmbeddingData`.  The conclusion is an actual e-p-pair
`EPPair (Bilimit S) E`. -/
def ExpandingSequence.BilimitSubdomainOfCoconeFull
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) :
    Prop :=
  (∀ n : Nat, IsDcpo (D n)) →
  (∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) →
  ∀ E : Type u, ∀ [Preorder E], IsDcpo E → ∀ C : ExpandingSequence.Cocone S E,
    Nonempty (ExpandingSequence.CoconeEmbeddingData S C) →
      ExpandingSequence.BilimitSubdomainOf S E

/-- A projection cone whose legs are projections in e-p-pairs. -/
structure ExpandingSequence.ProjectionConeProjectionData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.ProjectionCone S E) where
  ep : ∀ n : Nat, EPPair (D n) E
  ep_p : ∀ n : Nat, ∀ x : E, (ep n).p x = C.p n x

namespace ExpandingSequence.ProjectionConeProjectionData

variable {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
variable {S : ExpandingSequence D}
variable {E : Type u} [Preorder E]
variable {C : ExpandingSequence.ProjectionCone S E}
variable (hC : ExpandingSequence.ProjectionConeProjectionData S C)

/-- A projection cone whose legs are projection halves determines an embedding
cocone by taking the corresponding embedding halves. -/
def toCocone
    (hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.Cocone S E where
  f := fun n => (hC.ep n).e
  continuous := fun n => (hC.ep n).continuous_e
  commute := by
    intro n m h x
    apply hEanti
    · apply ((hC.ep m).toAdjunction.adj (S.e h x) ((hC.ep n).e x)).1
      have hproj :
          S.p h ((hC.ep m).p ((hC.ep n).e x)) = x := by
        calc
          S.p h ((hC.ep m).p ((hC.ep n).e x))
              = S.p h (C.p m ((hC.ep n).e x)) := by rw [hC.ep_p m]
          _ = C.p n ((hC.ep n).e x) := C.commute h _
          _ = (hC.ep n).p ((hC.ep n).e x) := by rw [hC.ep_p n]
          _ = x := (hC.ep n).retract x
      calc
        S.e h x = S.e h (S.p h ((hC.ep m).p ((hC.ep n).e x))) := by rw [hproj]
        _ ≤ (hC.ep m).p ((hC.ep n).e x) :=
          S.below h ((hC.ep m).p ((hC.ep n).e x))
    · apply ((hC.ep n).toAdjunction.adj x ((hC.ep m).e (S.e h x))).1
      have hproj :
          (hC.ep n).p ((hC.ep m).e (S.e h x)) = x := by
        calc
          (hC.ep n).p ((hC.ep m).e (S.e h x))
              = C.p n ((hC.ep m).e (S.e h x)) := hC.ep_p n _
          _ = S.p h (C.p m ((hC.ep m).e (S.e h x))) := (C.commute h _).symm
          _ = S.p h ((hC.ep m).p ((hC.ep m).e (S.e h x))) := by
              rw [hC.ep_p m]
          _ = S.p h (S.e h x) := by rw [(hC.ep m).retract]
          _ = x := S.retract h x
      rw [hproj]

/-- The embedding cocone induced by projection legs carries the same e-p-pairs. -/
def toCoconeEmbeddingData
    (hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.CoconeEmbeddingData S (hC.toCocone hEanti) where
  ep := hC.ep
  ep_e := by
    intro n x
    rfl

end ExpandingSequence.ProjectionConeProjectionData

/-- A projection cone whose legs are projection halves has the canonical
mediating map into the bilimit as a projection morphism. -/
theorem ExpandingSequence.projectionConeToBilimit_projectionMorphism
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    {C : ExpandingSequence.ProjectionCone S E}
    (hC : ExpandingSequence.ProjectionConeProjectionData S C) :
    ProjectionMorphism (ExpandingSequence.projectionConeToBilimit S C) := by
  let Cemb : ExpandingSequence.Cocone S E := hC.toCocone hEanti
  let hCemb : ExpandingSequence.CoconeEmbeddingData S Cemb :=
    hC.toCoconeEmbeddingData hEanti
  let hmap := ExpandingSequence.bilimitToCoconeEmbeddingData_canonical
    S hE hCemb hantisymm
  let ep : EPPair (Bilimit S) E :=
    { e := hmap.toFun
      p := hCemb.toBilimitOfAntisymm hantisymm
      continuous_e := hmap.continuous_toFun
      continuous_p := hCemb.toBilimitOfAntisymm_scottContinuous hantisymm
      retract := hmap.retract_toBilimit
      below := hmap.below_toFun }
  refine ⟨⟨ep, ?_⟩⟩
  intro y
  apply Subtype.ext
  funext n
  exact hC.ep_p n y

/-- Projection-leg restricted version of the limiting-cone interface used for
Corollary 3.3.10.

PDF text: "The bilimit of an expanding sequence is also the colimit (limit) in
the restricted category of dcpo's with embeddings (projections) as morphisms."
This interface records the parenthesized limit/projection half.

Current Lean spelling: the cone legs are required to be projection halves of
e-p-pairs, and the universal property is quantified only over cones with the
same projection-leg data.  The mediating map is returned both as an ordinary
continuous cone morphism and as the projection half of an e-p-pair. -/
def ExpandingSequence.IsRestrictedLimitingProjectionCone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (_hE : IsDcpo E)
    (_hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    (C : ExpandingSequence.ProjectionCone S E) : Prop :=
  Nonempty (ExpandingSequence.ProjectionConeProjectionData S C) ∧
    ∀ F : Type u, ∀ [Preorder F], IsDcpo F →
      (∀ x y : F, x ≤ y → y ≤ x → x = y) → ∀ C' : ExpandingSequence.ProjectionCone S F,
      Nonempty (ExpandingSequence.ProjectionConeProjectionData S C') →
        ∃ u : F → E, ExpandingSequence.ProjectionConeMediates S C' C u ∧
          ProjectionMorphism u ∧
          ∀ v : F → E, ExpandingSequence.ProjectionConeMediates S C' C v →
            ∀ y : F, v y = u y

/-- The canonical projection cone has projection morphisms in the restricted
projection category: each leg is the projection half of the e-p-pair
`(e_n,p_n)`. -/
noncomputable def ExpandingSequence.bilimitProjectionConeProjectionData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.ProjectionConeProjectionData S
      (S.bilimitProjectionCone hDdcpo hantisymm) where
  ep := S.stageEPPair hDdcpo hantisymm
  ep_p := by
    intro n x
    rfl

/-- The canonical projection cone satisfies the current projection-leg
restricted interface.  This upgrades the ordinary projection-limit result by
adding e-p-pair data for the canonical projections and packaging the mediating
map from any projection-leg cone as a projection morphism. -/
theorem ExpandingSequence.isRestrictedLimitingProjectionCone_bilimitProjectionCone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.IsRestrictedLimitingProjectionCone S
      (S.bilimit_dcpo_of_stage_dcpo hDdcpo hantisymm)
      (S.bilimit_antisymm_of_stage_antisymm hantisymm)
      (S.bilimitProjectionCone hDdcpo hantisymm) := by
  constructor
  · exact ⟨S.bilimitProjectionConeProjectionData hDdcpo hantisymm⟩
  · intro F _ hF hFanti C' hC'
    rcases hC' with ⟨hC'⟩
    refine ⟨ExpandingSequence.projectionConeToBilimit S C', ?_, ?_, ?_⟩
    · constructor
      · exact ExpandingSequence.projectionConeToBilimit_scottContinuous S C'
      · intro n x
        rfl
    · exact S.projectionConeToBilimit_projectionMorphism hantisymm hF hFanti hC'
    · intro v hv x
      apply Subtype.ext
      funext n
      exact hv.2 n x

/-- Embedding-leg restricted version of the colimiting-cocone interface used for
Corollary 3.3.10.

PDF text: "The bilimit of an expanding sequence is also the colimit (limit) in
the restricted category of dcpo's with embeddings (projections) as morphisms."
This interface records the colimit/embedding half.

Current Lean spelling: the cocone legs are required to be embedding halves of
e-p-pairs, and the universal property is quantified only over cocones with the
same embedding-leg data.  The mediating map is returned both as an ordinary
continuous cocone morphism and as the embedding half of an e-p-pair. -/
def ExpandingSequence.IsRestrictedColimitingEmbeddingCocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (_hE : IsDcpo E)
    (_hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    (C : ExpandingSequence.Cocone S E) : Prop :=
  Nonempty (ExpandingSequence.CoconeEmbeddingData S C) ∧
    ∀ F : Type u, ∀ [Preorder F], IsDcpo F →
      (∀ x y : F, x ≤ y → y ≤ x → x = y) → ∀ C' : ExpandingSequence.Cocone S F,
      Nonempty (ExpandingSequence.CoconeEmbeddingData S C') →
        ∃ u : E → F, ExpandingSequence.CoconeMediates S C C' u ∧
          EmbeddingMorphism u ∧
          ∀ v : E → F, ExpandingSequence.CoconeMediates S C C' v →
            ∀ y : E, v y = u y

/-- The canonical embedding cocone satisfies the current embedding-leg
restricted interface.  The proof uses the full Lemma 3.3.8 sufficiency
direction, because the canonical cocone has the e-p-pair decomposition
`⋁_n e_n ∘ p_n = id`; the mediating map is packaged as the canonical
bilimit-to-cocone embedding from Proposition 3.3.9. -/
theorem ExpandingSequence.isRestrictedColimitingEmbeddingCocone_bilimitEmbeddingCocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.IsRestrictedColimitingEmbeddingCocone S
      (S.bilimit_dcpo_of_stage_dcpo hDdcpo hantisymm)
      (S.bilimit_antisymm_of_stage_antisymm hantisymm)
      (S.bilimitEmbeddingCocone hantisymm) := by
  constructor
  · exact ⟨S.bilimitEmbeddingCoconeEmbeddingData hDdcpo hantisymm⟩
  · intro F _ hF hFanti C' hC'
    rcases hC' with ⟨hC'⟩
    let hmap := ExpandingSequence.bilimitToCoconeEmbeddingData_canonical
      S hF hC' hantisymm
    refine ⟨hmap.toFun, ?_, ?_, ?_⟩
    · change ExpandingSequence.CoconeMediates S (S.bilimitEmbeddingCocone hantisymm) C'
        (ExpandingSequence.bilimitToCoconeSup S hF C')
      exact S.bilimitToCoconeSup_mediates_bilimitEmbeddingCocone
        hDdcpo hantisymm hF hFanti hC'
    · let ep : EPPair (Bilimit S) F :=
        { e := hmap.toFun
          p := hC'.toBilimitOfAntisymm hantisymm
          continuous_e := hmap.continuous_toFun
          continuous_p := hC'.toBilimitOfAntisymm_scottContinuous hantisymm
          retract := hmap.retract_toBilimit
          below := hmap.below_toFun }
      refine ⟨⟨ep, ?_⟩⟩
      intro x
      rfl
    · have hcolim :
        ExpandingSequence.IsColimitingCocone S
          (S.bilimit_dcpo_of_stage_dcpo hDdcpo hantisymm)
          (S.bilimit_antisymm_of_stage_antisymm hantisymm)
          (S.bilimitEmbeddingCocone hantisymm) :=
        S.isColimitingCocone_of_epDecomposition hantisymm
          (S.bilimit_dcpo_of_stage_dcpo hDdcpo hantisymm)
          (S.bilimit_antisymm_of_stage_antisymm hantisymm)
          (S.bilimitEmbeddingCoconeEPDecomposition hDdcpo hantisymm)
      rcases hcolim F hF hFanti C' with ⟨u₀, hu₀, huniq⟩
      intro v hv y
      have hvu₀ := huniq v hv y
      have hmapu₀ : hmap.toFun y = u₀ y := by
        apply huniq hmap.toFun
        change ExpandingSequence.CoconeMediates S (S.bilimitEmbeddingCocone hantisymm) C'
          (ExpandingSequence.bilimitToCoconeSup S hF C')
        exact S.bilimitToCoconeSup_mediates_bilimitEmbeddingCocone
          hDdcpo hantisymm hF hFanti hC'
      exact hvu₀.trans hmapu₀.symm

/-- Current statement package for Corollary 3.3.10.

The package proves that the bilimit carrier has projection/embedding cone legs
of the restricted form and satisfies the corresponding universal properties
over cones/cocones whose legs are also restricted, with mediating maps packaged
as projection/embedding morphisms.  The uniqueness clause is stated for all
ordinary continuous cone/cocone mediating maps, hence is stronger than uniqueness
only among restricted morphisms. -/
structure ExpandingSequence.RestrictedBilimitColimitData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) where
  bilimit_dcpo : IsDcpo (Bilimit S)
  bilimit_antisymm : ∀ x y : Bilimit S, x ≤ y → y ≤ x → x = y
  projectionCone : ExpandingSequence.ProjectionCone S (Bilimit S)
  projectionCone_proj : ∀ n : Nat, ∀ x : Bilimit S, projectionCone.p n x = Bilimit.proj S n x
  limiting_projection :
    ExpandingSequence.IsRestrictedLimitingProjectionCone S bilimit_dcpo bilimit_antisymm projectionCone
  embeddingCocone : ExpandingSequence.Cocone S (Bilimit S)
  colimiting_embedding :
    ExpandingSequence.IsRestrictedColimitingEmbeddingCocone S bilimit_dcpo bilimit_antisymm embeddingCocone

/-- Corollary 3.3.10 current statement predicate: projection and embedding
legs are restricted, and the mediating morphisms are packaged as the matching
projection/embedding halves of e-p-pairs. -/
def ExpandingSequence.RestrictedBilimitColimitCoincidence
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) :
    Prop :=
  (∀ n : Nat, IsDcpo (D n)) →
    (∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) →
      Nonempty (ExpandingSequence.RestrictedBilimitColimitData S)

/-- Lemma 3.3.8 necessity direction: a colimiting cocone is isomorphic to the
explicit bilimit cocone, so the projections are obtained as `g_n = p_n ∘ u`,
where `u : E -> Bilimit S` is the unique mediating map into the canonical
embedding cocone. -/
theorem ExpandingSequence.coconeEPDecomposition_of_isColimitingCocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    {C : ExpandingSequence.Cocone S E}
    (hcolimiting : ExpandingSequence.IsColimitingCocone S hE hEanti C) :
    Nonempty (ExpandingSequence.CoconeEPDecomposition S C) := by
  let hBdcpo : IsDcpo (Bilimit S) := S.bilimit_dcpo_of_stage_dcpo hDdcpo hantisymm
  let hBanti : ∀ x y : Bilimit S, x ≤ y → y ≤ x → x = y :=
    S.bilimit_antisymm_of_stage_antisymm hantisymm
  let CB : ExpandingSequence.Cocone S (Bilimit S) := S.bilimitEmbeddingCocone hantisymm
  have hBcolimiting : ExpandingSequence.IsColimitingCocone S hBdcpo hBanti CB :=
    S.isColimitingCocone_of_epDecomposition hantisymm hBdcpo hBanti
      (S.bilimitEmbeddingCoconeEPDecomposition hDdcpo hantisymm)
  rcases hcolimiting (Bilimit S) hBdcpo hBanti CB with ⟨u, hu, _huuniq⟩
  rcases hBcolimiting E hE hEanti C with ⟨v, hv, _hvuniq⟩
  rcases hcolimiting E hE hEanti C with ⟨w, _hw, hwuniq⟩
  have hid : ExpandingSequence.CoconeMediates S C C (fun y : E => y) := by
    constructor
    · exact scottContinuous_id
    · intro n x
      rfl
  have hvuMed : ExpandingSequence.CoconeMediates S C C (fun y : E => v (u y)) := by
    constructor
    · exact ScottContinuous.comp hv.1 hu.1
    · intro n x
      calc
        v (u (C.f n x)) = v (CB.f n x) := by rw [hu.2 n x]
        _ = C.f n x := hv.2 n x
  have hvu : ∀ y : E, v (u y) = y := by
    intro y
    have hcomp : v (u y) = w y := hwuniq (fun y : E => v (u y)) hvuMed y
    have hidw : y = w y := hwuniq (fun y : E => y) hid y
    exact hcomp.trans hidw.symm
  let epFun : ∀ n : Nat, EPPair (D n) E := fun n =>
    { e := C.f n
      p := fun y : E => Bilimit.proj S n (u y)
      continuous_e := C.continuous n
      continuous_p :=
        ScottContinuous.comp
          (S.bilimitProj_scottContinuous_of_stage_dcpo hDdcpo hantisymm n) hu.1
      retract := by
        intro x
        calc
          Bilimit.proj S n (u (C.f n x))
              = Bilimit.proj S n (CB.f n x) := by rw [hu.2 n x]
          _ = x := by
              change Bilimit.proj S n (S.stageEmbedding hantisymm n x) = x
              exact (S.stageEPPair hDdcpo hantisymm n).retract x
      below := by
        intro y
        calc
          C.f n (Bilimit.proj S n (u y))
              = v (CB.f n (Bilimit.proj S n (u y))) := (hv.2 n _).symm
          _ ≤ v (u y) := by
              exact hv.1.1 ((S.stageEPPair hDdcpo hantisymm n).below (u y))
          _ = y := hvu y }
  refine ⟨{
    ep := epFun
    ep_e := by
      intro n x
      rfl
    sup_identity := ?_
  }⟩
  intro y
  constructor
  · intro z hz
    rcases hz with ⟨n, rfl⟩
    exact (epFun n).below y
  · intro b hb
    have hcanon :=
      (S.bilimitEmbeddingCoconeEPDecomposition hDdcpo hantisymm).sup_identity (u y)
    have hub : IsUpperBound
        ({z : Bilimit S |
          ∃ n : Nat,
            z = (S.stageEPPair hDdcpo hantisymm n).e
              ((S.stageEPPair hDdcpo hantisymm n).p (u y))} : Set (Bilimit S))
        (u b) := by
      intro z hz
      rcases hz with ⟨n, rfl⟩
      have hsource : C.f n (Bilimit.proj S n (u y)) ≤ b :=
        hb ⟨n, rfl⟩
      have hstage :
          (S.stageEPPair hDdcpo hantisymm n).e
              ((S.stageEPPair hDdcpo hantisymm n).p (u y)) =
            u (C.f n (Bilimit.proj S n (u y))) := by
        simpa [ExpandingSequence.stageEPPair, CB, ExpandingSequence.bilimitEmbeddingCocone]
          using (hu.2 n (Bilimit.proj S n (u y))).symm
      rw [hstage]
      exact hu.1.1 hsource
    have huyub : u y ≤ u b := hcanon.2 (u b) (by
      intro z hz
      rcases hz with ⟨n, rfl⟩
      exact hub ⟨n, rfl⟩)
    calc
      y = v (u y) := (hvu y).symm
      _ ≤ v (u b) := hv.1.1 huyub
      _ = b := hvu b

/-- Legacy weak map-out predicate for an expanding sequence: a family of
continuous maps out of the stages, together with reverse continuous maps, gives a
map out of the explicit bilimit carrier.  It does not encode the cocone
commuting equations; the full cocone criterion is
`ColimitingCoconeCriterionFull`. -/
def ExpandingSequence.ColimitingCoconeCriterion
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) : Prop :=
  ∀ E : Type u, ∀ [Preorder E],
    (∃ f : ∀ n : Nat, D n → E, ∃ g : ∀ n : Nat, E → D n,
      ∀ n : Nat, ScottContinuous (f n) ∧ ScottContinuous (g n)) →
      Nonempty (Bilimit S → E)

/-- Lemma 3.3.8, legacy weak predicate: a family of stage maps induces a map out
of the bilimit carrier by using the zeroth projection.  This is weaker than the
full colimiting-cocone criterion in the book and does not encode the cocone
commuting equations. -/
theorem lemma_3_3_8_expanding_sequence_colimiting_cocone_criterion_legacy
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D) : ExpandingSequence.ColimitingCoconeCriterion S := by
  intro E _ h
  rcases h with ⟨f, _g, _hfg⟩
  exact ⟨fun x => f 0 (Bilimit.proj S 0 x)⟩

/-- Lemma 3.3.8, full statement.

PDF text excerpt: "It is colimiting if and only if" the cocone maps come with
Scott-continuous e-p-pair projections `g_n : E → D_n` and satisfy
`⋁_{n∈N} f_n ∘ g_n = id_E`.

Current Lean spelling: prove both directions of the PDF criterion in the
preorder setting of `ColimitingCoconeCriterionFull`. -/
theorem lemma_3_3_8_expanding_sequence_colimiting_cocone_criterion
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D) : ExpandingSequence.ColimitingCoconeCriterionFull S := by
  intro hDdcpo hantisymm E _ hE hEanti C
  constructor
  · intro hcolimiting
    exact ExpandingSequence.coconeEPDecomposition_of_isColimitingCocone
      S hDdcpo hantisymm hE hEanti hcolimiting
  · intro hdecomp
    rcases hdecomp with ⟨h⟩
    exact ExpandingSequence.isColimitingCocone_of_epDecomposition
      S hantisymm hE hEanti h

/-- Legacy weak map-to-carrier predicate for Proposition 3.3.9: a family of
continuous stage maps supplies a map from the bilimit carrier to the target.
This does not assert an embedding, projection, or cocone commuting law. -/
def ExpandingSequence.BilimitSubdomainOfCocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) : Prop :=
  ∀ E : Type u, ∀ [Preorder E],
    (∃ f : ∀ n : Nat, D n → E, ∀ n : Nat, ScottContinuous (f n)) →
      Nonempty (Bilimit S → E)

/-- Proposition 3.3.9, legacy weak predicate: a family of stage maps supplies a
zeroth-projection map from the bilimit carrier.  PDF text: "where the `f_n` are
embeddings. Then the bilimit of the sequence is a sub-domain of `E`."  This
legacy predicate is weaker than the full subdomain embedding statement in the
book. -/
theorem prop_3_3_9_bilimit_subdomain_of_cocone_legacy
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D) : ExpandingSequence.BilimitSubdomainOfCocone S := by
  intro E _ h
  rcases h with ⟨f, _hf⟩
  exact ⟨fun x => f 0 (Bilimit.proj S 0 x)⟩

/-- Proposition 3.3.9, full preorder-interface statement.

PDF text: "Let `⟨E,(f_n)_{n∈N}⟩` be a cocone over the expanding sequence
`⟨(D_n)_{n∈N}, (e_mn : D_n → D_m)_{n≤m∈N}⟩` where the `f_n` are embeddings.
Then the bilimit of the sequence is a sub-domain of `E`."

Current Lean spelling: for any dcpo cocone carrier whose legs are supplied as
embeddings, the bilimit embeds as a sub-domain of the cocone carrier via the
canonical supremum map. -/
theorem prop_3_3_9_bilimit_subdomain_of_cocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D) : ExpandingSequence.BilimitSubdomainOfCoconeFull S := by
  intro _hDdcpo hantisymm E _ hE C hCNonempty
  rcases hCNonempty with ⟨hC⟩
  exact ExpandingSequence.bilimitSubdomainOf_of_embeddingData_canonical
    S hE C hC hantisymm

/-- Legacy weak limit-colimit coincidence predicate: packages only the current
carrier/projection data and the weak map-out predicate. -/
def ExpandingSequence.BilimitColimitCoincidence
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) : Prop :=
  ExpandingSequence.BilimitTheoremData S ∧ ExpandingSequence.ColimitingCoconeCriterion S

/-- Corollary 3.3.10, lightweight interface: packages the current bilimit carrier
data and weak colimiting-cocone criterion. -/
theorem cor_3_3_10_bilimit_colimit_embedding_projection_legacy
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D) : ExpandingSequence.BilimitColimitCoincidence S := by
  exact ⟨theorem_3_3_7_expanding_sequence_bilimit_legacy S,
    lemma_3_3_8_expanding_sequence_colimiting_cocone_criterion_legacy S⟩

/-- Corollary 3.3.10, current preorder-interface statement.

PDF text: "The bilimit of an expanding sequence is also the colimit (limit) in
the restricted category of dcpo's with embeddings (projections) as morphisms."

Current Lean spelling: the canonical bilimit cones have the required
embedding/projection legs and satisfy universal properties against cones with
the same kind of restricted legs.  The universal mediating maps are now
packaged as embedding/projection morphisms, with uniqueness stated against all
ordinary continuous mediating maps. -/
theorem cor_3_3_10_bilimit_colimit_embedding_projection
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D) :
    ExpandingSequence.RestrictedBilimitColimitCoincidence S := by
  intro hDdcpo hantisymm
  exact ⟨{
    bilimit_dcpo := S.bilimit_dcpo_of_stage_dcpo hDdcpo hantisymm
    bilimit_antisymm := S.bilimit_antisymm_of_stage_antisymm hantisymm
    projectionCone := S.bilimitProjectionCone hDdcpo hantisymm
    projectionCone_proj := by
      intro n x
      rfl
    limiting_projection :=
      S.isRestrictedLimitingProjectionCone_bilimitProjectionCone hDdcpo hantisymm
    embeddingCocone := S.bilimitEmbeddingCocone hantisymm
    colimiting_embedding :=
      S.isRestrictedColimitingEmbeddingCocone_bilimitEmbeddingCocone hDdcpo hantisymm
  }⟩


end Chapter3
end AbramskyJung

import Practice.DomainTheory.Chapter03.NumberedItems.Section33_Limits

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Chapter 3: Section 3.3 bilimit construction

Book-facing declarations and their local support API are kept together in
textbook dependency order. Reusable constructions remain in the concept-owned
`Chapter03.Section*` modules.
-/

universe u v w z l

namespace AbramskyJung
namespace Chapter3

/-- Legacy weak carrier/projection witness for Theorem 3.3.7.

PDF text excerpt for Theorem 3.3.7: "Let `⟨(D_n)_{n∈N},
(e_mn : D_n → D_m)_{n≤m∈N}⟩` be an expanding sequence in `DCPO`. Define an
object `D` by compatible tuples `x_n = p_nm(x_m)`; projections `p_m : D → D_m`;
and embeddings `e_m : D_m → D` by the stage-coordinate formula. Then the maps
`(e_m,p_m)` form embedding-projection pairs with `⋁_m e_m ∘ p_m = id_D`,
`⟨D,(p_n)⟩` is a limit of the projection diagram, and `⟨D,(e_n)⟩` is a colimit
of the embedding diagram."

Current Lean spelling of this legacy witness: it only records the explicit
bilimit carrier predicate and the existence of the coordinate projection maps;
the full limit-colimit content is represented by the later projection-cone and
embedding-cocone theorems. -/
structure ExpandingSequence.BilimitTheoremData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) : Prop where
  carrier_eq : ∀ x : Bilimit S, BilimitCarrier S x.1
  projection : ∀ n : Nat, Nonempty (Bilimit S → D n)

/-- Theorem 3.3.7 legacy partial carrier/projection data for the bilimit of an
expanding sequence.  Full limit-colimit universal properties are tracked and
proved separately below. -/
theorem theorem_3_3_7_expanding_sequence_bilimit_legacy
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D) : ExpandingSequence.BilimitTheoremData S := by
  exact ⟨fun x => x.2, fun n => ⟨Bilimit.proj S n⟩⟩

instance bilimitPreorder
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) :
    Preorder (Bilimit S) where
  le x y := ∀ n : Nat, x.1 n ≤ y.1 n
  le_refl x n := le_rfl
  le_trans x y z hxy hyz n := le_trans (hxy n) (hyz n)

/-- A cocone over an expanding sequence, with maps `f_n : D_n -> E` commuting
with the embeddings `e_{n,m}`. -/
structure ExpandingSequence.Cocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (E : Type u) [Preorder E] where
  f : ∀ n : Nat, D n → E
  continuous : ∀ n : Nat, ScottContinuous (f n)
  commute : ∀ {n m : Nat} (h : n ≤ m) (x : D n), f m (S.e h x) = f n x

/-- A cone over the projection side of an expanding sequence, with maps
`p_n : E -> D_n` commuting with the projections `p_{n,m}`. -/
structure ExpandingSequence.ProjectionCone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (E : Type u) [Preorder E] where
  p : ∀ n : Nat, E → D n
  continuous : ∀ n : Nat, ScottContinuous (p n)
  commute : ∀ {n m : Nat} (h : n ≤ m) (x : E), S.p h (p m x) = p n x

/-- A map between cocone carriers mediates the two cocones. -/
def ExpandingSequence.CoconeMediates
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E F : Type u} [Preorder E] [Preorder F]
    (C : ExpandingSequence.Cocone S E) (C' : ExpandingSequence.Cocone S F)
    (u : E → F) : Prop :=
  ScottContinuous u ∧ ∀ n : Nat, ∀ x : D n, u (C.f n x) = C'.f n x

/-- A cocone is colimiting in `DCPO` when every cocone with dcpo carrier has a
unique continuous mediating map from its carrier. -/
def ExpandingSequence.IsColimitingCocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (_hE : IsDcpo E)
    (_hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    (C : ExpandingSequence.Cocone S E) : Prop :=
  ∀ F : Type u, ∀ [Preorder F], IsDcpo F →
    (∀ x y : F, x ≤ y → y ≤ x → x = y) → ∀ C' : ExpandingSequence.Cocone S F,
    ∃ u : E → F, ExpandingSequence.CoconeMediates S C C' u ∧
      ∀ v : E → F, ExpandingSequence.CoconeMediates S C C' v → ∀ y : E, v y = u y

/-- A map between projection-cone carriers mediates the two projection cones. -/
def ExpandingSequence.ProjectionConeMediates
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E F : Type u} [Preorder E] [Preorder F]
    (C : ExpandingSequence.ProjectionCone S E)
    (C' : ExpandingSequence.ProjectionCone S F) (u : E → F) : Prop :=
  ScottContinuous u ∧ ∀ n : Nat, ∀ x : E, C'.p n (u x) = C.p n x

/-- A map represented as the embedding half of an e-p-pair. -/
def EmbeddingMorphism {E F : Type u} [Preorder E] [Preorder F] (u : E → F) : Prop :=
  Nonempty {ep : EPPair E F // ∀ x : E, ep.e x = u x}

/-- A map represented as the projection half of an e-p-pair. -/
def ProjectionMorphism {E F : Type u} [Preorder E] [Preorder F] (u : E → F) : Prop :=
  Nonempty {ep : EPPair F E // ∀ x : E, ep.p x = u x}

/-- A projection cone is limiting in `DCPO` when every projection cone with dcpo
carrier has a unique continuous mediating map into its carrier. -/
def ExpandingSequence.IsLimitingProjectionCone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (_hE : IsDcpo E)
    (_hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    (C : ExpandingSequence.ProjectionCone S E) : Prop :=
  ∀ F : Type u, ∀ [Preorder F], IsDcpo F →
    (∀ x y : F, x ≤ y → y ≤ x → x = y) → ∀ C' : ExpandingSequence.ProjectionCone S F,
    ∃ u : F → E, ExpandingSequence.ProjectionConeMediates S C' C u ∧
      ∀ v : F → E, ExpandingSequence.ProjectionConeMediates S C' C v → ∀ y : F, v y = u y

/-- The e-p-pair decomposition of the cocone maps in Lemma 3.3.8.

PDF text excerpt: a cocone `⟨E,(f_n)_{n∈N}⟩` is colimiting iff "there are
Scott-continuous functions `g_n : E → D_n` such that each `(f_n,g_n)` is an
e-p-pair and, secondly, `⋁_{n∈N} f_n ∘ g_n = id_E` holds."

Current Lean spelling: the projections are represented by the projection halves
of `EPPair (D n) E`, and the supremum identity is recorded pointwise as an
`IsSup` statement for `{f_n(g_n(y)) | n ∈ Nat}`. -/
structure ExpandingSequence.CoconeEPDecomposition
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.Cocone S E) where
  ep : ∀ n : Nat, EPPair (D n) E
  ep_e : ∀ n : Nat, ∀ x : D n, (ep n).e x = C.f n x
  sup_identity :
    ∀ y : E, IsSup ({z : E | ∃ n : Nat, z = (ep n).e ((ep n).p y)} : Set E) y

/-- The statement form of Lemma 3.3.8.

PDF text excerpt: "Let `⟨E,(f_n)_{n∈N}⟩` be a cocone for the expanding sequence
`⟨(D_n)_{n∈N},(e_mn : D_n → D_m)_{n≤m∈N}⟩`. It is colimiting if and only if,
firstly, there are Scott-continuous functions `g_n : E → D_n` such that each
`(f_n,g_n)` is an e-p-pair and, secondly, `⋁_{n∈N} f_n ∘ g_n = id_E` holds."

Current Lean spelling: the iff is stated for preorder carriers under explicit
stage dcpo/antisymmetry hypotheses and explicit dcpo/antisymmetry hypotheses on
the cocone carrier. -/
def ExpandingSequence.ColimitingCoconeCriterionFull
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) :
  Prop :=
  (∀ n : Nat, IsDcpo (D n)) →
  (∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) →
  ∀ E : Type u, ∀ [Preorder E], ∀ hE : IsDcpo E,
    ∀ hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y, ∀ C : ExpandingSequence.Cocone S E,
    ExpandingSequence.IsColimitingCocone S hE hEanti C ↔
      Nonempty (ExpandingSequence.CoconeEPDecomposition S C)

/-- A cocone whose legs are embeddings, represented by e-p-pairs whose embedding
components are the cocone maps. -/
structure ExpandingSequence.CoconeEmbeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.Cocone S E) where
  ep : ∀ n : Nat, EPPair (D n) E
  ep_e : ∀ n : Nat, ∀ x : D n, (ep n).e x = C.f n x

namespace ExpandingSequence.CoconeEmbeddingData

variable {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
variable {S : ExpandingSequence D}
variable {E : Type u} [Preorder E]
variable {C : ExpandingSequence.Cocone S E}
variable (hC : ExpandingSequence.CoconeEmbeddingData S C)

/-- Projection coordinates from an embedding cocone commute up to the first
inequality needed for the bilimit carrier equation. -/
theorem projection_commute_le_left {n m : Nat} (h : n ≤ m) (y : E) :
    S.p h ((hC.ep m).p y) ≤ (hC.ep n).p y := by
  apply ((hC.ep n).toAdjunction.adj (S.p h ((hC.ep m).p y)) y).2
  calc
    (hC.ep n).e (S.p h ((hC.ep m).p y))
        = C.f n (S.p h ((hC.ep m).p y)) := hC.ep_e n _
    _ = C.f m (S.e h (S.p h ((hC.ep m).p y))) := (C.commute h _).symm
    _ ≤ C.f m ((hC.ep m).p y) := (C.continuous m).1 (S.below h ((hC.ep m).p y))
    _ = (hC.ep m).e ((hC.ep m).p y) := (hC.ep_e m _).symm
    _ ≤ y := (hC.ep m).below y

/-- Projection coordinates from an embedding cocone commute up to the second
inequality needed for the bilimit carrier equation. -/
theorem projection_commute_le_right {n m : Nat} (h : n ≤ m) (y : E) :
    (hC.ep n).p y ≤ S.p h ((hC.ep m).p y) := by
  have hleToM : S.e h ((hC.ep n).p y) ≤ (hC.ep m).p y := by
    apply ((hC.ep m).toAdjunction.adj (S.e h ((hC.ep n).p y)) y).2
    calc
      (hC.ep m).e (S.e h ((hC.ep n).p y))
          = C.f m (S.e h ((hC.ep n).p y)) := hC.ep_e m _
      _ = C.f n ((hC.ep n).p y) := C.commute h _
      _ = (hC.ep n).e ((hC.ep n).p y) := (hC.ep_e n _).symm
      _ ≤ y := (hC.ep n).below y
  have hmono := (S.continuous_p h).1 hleToM
  simpa [S.retract h ((hC.ep n).p y)] using hmono

/-- With explicit antisymmetry for the stage orders, the projection coordinates
of an embedding cocone form a compatible bilimit tuple. -/
theorem projection_commute_of_antisymm
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {n m : Nat} (h : n ≤ m) (y : E) :
    (hC.ep n).p y = S.p h ((hC.ep m).p y) :=
  hantisymm n _ _
    (hC.projection_commute_le_right h y)
    (hC.projection_commute_le_left h y)

/-- The projection part of the e-p-pair in Proposition 3.3.9, constructed as a
map into the explicit bilimit carrier under explicit antisymmetry of the stage
orders. -/
def toBilimitOfAntisymm
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    E → Bilimit S :=
  fun y => ⟨fun n => (hC.ep n).p y, by
    intro n m h
    exact hC.projection_commute_of_antisymm hantisymm h y⟩

/-- The projection map `E -> Bilimit S` built from an embedding cocone is
monotone, because each coordinate projection in the e-p-pairs is monotone. -/
theorem toBilimitOfAntisymm_monotone
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    Monotone (hC.toBilimitOfAntisymm hantisymm) := by
  intro x y hxy n
  exact ((hC.ep n).continuous_p).1 hxy

/-- The projection map `E -> Bilimit S` built from an embedding cocone is
Scott-continuous.  Suprema in the explicit bilimit order are checked
coordinatewise. -/
theorem toBilimitOfAntisymm_scottContinuous
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ScottContinuous (hC.toBilimitOfAntisymm hantisymm) := by
  constructor
  · exact hC.toBilimitOfAntisymm_monotone hantisymm
  · intro A y hA hy
    constructor
    · intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact hC.toBilimitOfAntisymm_monotone hantisymm (hy.1 ha)
    · intro b hb n
      have hcoordSup : IsSup ((hC.ep n).p '' A) ((hC.ep n).p y) :=
        ((hC.ep n).continuous_p).2 hA hy
      exact hcoordSup.2 (b.1 n) (by
        intro z hz
        rcases hz with ⟨a, ha, rfl⟩
        exact hb ⟨a, ha, rfl⟩ n)

end ExpandingSequence.CoconeEmbeddingData

namespace ExpandingSequence.CoconeEPDecomposition

variable {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
variable {S : ExpandingSequence D}
variable {E : Type u} [Preorder E]
variable {C : ExpandingSequence.Cocone S E}

/-- The e-p-pair decomposition in Lemma 3.3.8 forgets to the embedding-cocone
data used in Proposition 3.3.9. -/
def toEmbeddingData (h : ExpandingSequence.CoconeEPDecomposition S C) :
    ExpandingSequence.CoconeEmbeddingData S C where
  ep := h.ep
  ep_e := h.ep_e

/-- The source-side family `{f_n(g_n(y))}` from Lemma 3.3.8. -/
def SourceImage (h : ExpandingSequence.CoconeEPDecomposition S C) (y : E) : Set E :=
  {z | ∃ n : Nat, z = (h.ep n).e ((h.ep n).p y)}

/-- The source-side family `{f_n(g_n(y))}` is directed. -/
theorem sourceImage_directed
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (y : E) : DirectedSet (h.SourceImage y) := by
  constructor
  · exact ⟨(h.ep 0).e ((h.ep 0).p y), ⟨0, rfl⟩⟩
  · intro a ha b hb
    rcases ha with ⟨n, rfl⟩
    rcases hb with ⟨m, rfl⟩
    let k : Nat := max n m
    refine ⟨(h.ep k).e ((h.ep k).p y), ⟨k, rfl⟩, ?_, ?_⟩
    · have hnk : n ≤ k := Nat.le_max_left n m
      have hcoord : (h.ep n).p y = S.p hnk ((h.ep k).p y) := by
        simpa [toEmbeddingData] using
          (h.toEmbeddingData.projection_commute_of_antisymm hantisymm hnk y)
      calc
        (h.ep n).e ((h.ep n).p y)
            = C.f n ((h.ep n).p y) := h.ep_e n _
        _ = C.f n (S.p hnk ((h.ep k).p y)) := by rw [hcoord]
        _ = C.f k (S.e hnk (S.p hnk ((h.ep k).p y))) :=
              (C.commute hnk (S.p hnk ((h.ep k).p y))).symm
        _ ≤ C.f k ((h.ep k).p y) :=
              (C.continuous k).1 (S.below hnk ((h.ep k).p y))
        _ = (h.ep k).e ((h.ep k).p y) := (h.ep_e k _).symm
    · have hmk : m ≤ k := Nat.le_max_right n m
      have hcoord : (h.ep m).p y = S.p hmk ((h.ep k).p y) := by
        simpa [toEmbeddingData] using
          (h.toEmbeddingData.projection_commute_of_antisymm hantisymm hmk y)
      calc
        (h.ep m).e ((h.ep m).p y)
            = C.f m ((h.ep m).p y) := h.ep_e m _
        _ = C.f m (S.p hmk ((h.ep k).p y)) := by rw [hcoord]
        _ = C.f k (S.e hmk (S.p hmk ((h.ep k).p y))) :=
              (C.commute hmk (S.p hmk ((h.ep k).p y))).symm
        _ ≤ C.f k ((h.ep k).p y) :=
              (C.continuous k).1 (S.below hmk ((h.ep k).p y))
        _ = (h.ep k).e ((h.ep k).p y) := (h.ep_e k _).symm

/-- The target-side family `{f'_n(g_n(y))}` used to define the mediating map
from a decomposed cocone to another cocone. -/
def TargetImage (h : ExpandingSequence.CoconeEPDecomposition S C)
    {F : Type u} [Preorder F] (C' : ExpandingSequence.Cocone S F) (y : E) : Set F :=
  {z | ∃ n : Nat, z = C'.f n ((h.ep n).p y)}

/-- The target-side family `{f'_n(g_n(y))}` is directed. -/
theorem targetImage_directed
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (C' : ExpandingSequence.Cocone S F) (y : E) :
    DirectedSet (h.TargetImage C' y) := by
  constructor
  · exact ⟨C'.f 0 ((h.ep 0).p y), ⟨0, rfl⟩⟩
  · intro a ha b hb
    rcases ha with ⟨n, rfl⟩
    rcases hb with ⟨m, rfl⟩
    let k : Nat := max n m
    refine ⟨C'.f k ((h.ep k).p y), ⟨k, rfl⟩, ?_, ?_⟩
    · have hnk : n ≤ k := Nat.le_max_left n m
      have hcoord : (h.ep n).p y = S.p hnk ((h.ep k).p y) := by
        simpa [toEmbeddingData] using
          (h.toEmbeddingData.projection_commute_of_antisymm hantisymm hnk y)
      calc
        C'.f n ((h.ep n).p y)
            = C'.f n (S.p hnk ((h.ep k).p y)) := by rw [hcoord]
        _ = C'.f k (S.e hnk (S.p hnk ((h.ep k).p y))) :=
              (C'.commute hnk (S.p hnk ((h.ep k).p y))).symm
        _ ≤ C'.f k ((h.ep k).p y) :=
              (C'.continuous k).1 (S.below hnk ((h.ep k).p y))
    · have hmk : m ≤ k := Nat.le_max_right n m
      have hcoord : (h.ep m).p y = S.p hmk ((h.ep k).p y) := by
        simpa [toEmbeddingData] using
          (h.toEmbeddingData.projection_commute_of_antisymm hantisymm hmk y)
      calc
        C'.f m ((h.ep m).p y)
            = C'.f m (S.p hmk ((h.ep k).p y)) := by rw [hcoord]
        _ = C'.f k (S.e hmk (S.p hmk ((h.ep k).p y))) :=
              (C'.commute hmk (S.p hmk ((h.ep k).p y))).symm
        _ ≤ C'.f k ((h.ep k).p y) :=
              (C'.continuous k).1 (S.below hmk ((h.ep k).p y))

/-- The canonical mediating map supplied by a Lemma 3.3.8 e-p-pair
decomposition, defined as `y ↦ ⋁_n f'_n(g_n(y))`. -/
noncomputable def mediatingSup
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (hF : IsDcpo F)
    (C' : ExpandingSequence.Cocone S F) : E → F :=
  fun y => Classical.choose (hF _ (h.targetImage_directed hantisymm C' y))

/-- The canonical mediating map is the supremum of its target-side image family. -/
theorem mediatingSup_isSup
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (hF : IsDcpo F)
    (C' : ExpandingSequence.Cocone S F) (y : E) :
    IsSup (h.TargetImage C' y) (h.mediatingSup hantisymm hF C' y) :=
  Classical.choose_spec (hF _ (h.targetImage_directed hantisymm C' y))

/-- The canonical mediating map is monotone. -/
theorem mediatingSup_monotone
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (hF : IsDcpo F)
    (C' : ExpandingSequence.Cocone S F) :
    Monotone (h.mediatingSup hantisymm hF C') := by
  intro x y hxy
  exact (h.mediatingSup_isSup hantisymm hF C' x).2
    (h.mediatingSup hantisymm hF C' y) (by
      intro z hz
      rcases hz with ⟨n, rfl⟩
      calc
        C'.f n ((h.ep n).p x)
            ≤ C'.f n ((h.ep n).p y) := (C'.continuous n).1 ((h.ep n).continuous_p.1 hxy)
        _ ≤ h.mediatingSup hantisymm hF C' y :=
            (h.mediatingSup_isSup hantisymm hF C' y).1 ⟨n, rfl⟩)

/-- The canonical mediating map preserves directed suprema. -/
theorem mediatingSup_scottContinuous
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (hF : IsDcpo F)
    (C' : ExpandingSequence.Cocone S F) :
    ScottContinuous (h.mediatingSup hantisymm hF C') := by
  constructor
  · exact h.mediatingSup_monotone hantisymm hF C'
  · intro A y hA hy
    constructor
    · intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact h.mediatingSup_monotone hantisymm hF C' (hy.1 ha)
    · intro b hb
      exact (h.mediatingSup_isSup hantisymm hF C' y).2 b (by
        intro z hz
        rcases hz with ⟨n, rfl⟩
        have hprojSup : IsSup ((h.ep n).p '' A) ((h.ep n).p y) :=
          ((h.ep n).continuous_p).2 hA hy
        have hstageSup :
            IsSup (C'.f n '' ((h.ep n).p '' A)) (C'.f n ((h.ep n).p y)) :=
          (C'.continuous n).2
            (DirectedSet.image ((h.ep n).continuous_p).1 hA) hprojSup
        exact hstageSup.2 b (by
          intro w hw
          rcases hw with ⟨ga, hga, rfl⟩
          rcases hga with ⟨a, ha, rfl⟩
          calc
            C'.f n ((h.ep n).p a)
                ≤ h.mediatingSup hantisymm hF C' a :=
                    (h.mediatingSup_isSup hantisymm hF C' a).1 ⟨n, rfl⟩
            _ ≤ b := hb ⟨a, ha, rfl⟩))

/-- At a cocone stage point `f_n(x)`, the target-side image family has supremum
`f'_n(x)`. -/
theorem targetImage_stage_isSup
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (C' : ExpandingSequence.Cocone S F)
    (n : Nat) (x : D n) :
    IsSup (h.TargetImage C' (C.f n x)) (C'.f n x) := by
  have hpn : (h.ep n).p (C.f n x) = x := by
    calc
      (h.ep n).p (C.f n x)
          = (h.ep n).p ((h.ep n).e x) := by rw [(h.ep_e n x).symm]
      _ = x := (h.ep n).retract x
  constructor
  · intro z hz
    rcases hz with ⟨m, rfl⟩
    rcases Nat.le_total n m with hnm | hmn
    · have hpm : (h.ep m).p (C.f n x) = S.e hnm x := by
        calc
          (h.ep m).p (C.f n x)
              = (h.ep m).p (C.f m (S.e hnm x)) := by rw [(C.commute hnm x).symm]
          _ = (h.ep m).p ((h.ep m).e (S.e hnm x)) := by
              rw [(h.ep_e m (S.e hnm x)).symm]
          _ = S.e hnm x := (h.ep m).retract (S.e hnm x)
      calc
        C'.f m ((h.ep m).p (C.f n x))
            = C'.f m (S.e hnm x) := by rw [hpm]
        _ = C'.f n x := C'.commute hnm x
        _ ≤ C'.f n x := le_rfl
    · have hcoord : (h.ep m).p (C.f n x) = S.p hmn ((h.ep n).p (C.f n x)) := by
        simpa [toEmbeddingData] using
          (h.toEmbeddingData.projection_commute_of_antisymm hantisymm hmn (C.f n x))
      calc
        C'.f m ((h.ep m).p (C.f n x))
            = C'.f m (S.p hmn x) := by rw [hcoord, hpn]
        _ = C'.f n (S.e hmn (S.p hmn x)) :=
            (C'.commute hmn (S.p hmn x)).symm
        _ ≤ C'.f n x := (C'.continuous n).1 (S.below hmn x)
  · intro b hb
    exact hb ⟨n, by rw [hpn]⟩

/-- The canonical supremum map commutes with the source and target cocone legs. -/
theorem mediatingSup_commute
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (hF : IsDcpo F)
    (hFanti : ∀ x y : F, x ≤ y → y ≤ x → x = y)
    (C' : ExpandingSequence.Cocone S F) :
    ∀ n : Nat, ∀ x : D n,
      h.mediatingSup hantisymm hF C' (C.f n x) = C'.f n x := by
  intro n x
  have hchosen := h.mediatingSup_isSup hantisymm hF C' (C.f n x)
  have hstage := h.targetImage_stage_isSup hantisymm C' n x
  exact hFanti _ _
    (hchosen.2 (C'.f n x) hstage.1)
    (hstage.2 (h.mediatingSup hantisymm hF C' (C.f n x)) hchosen.1)

/-- The canonical supremum map is a cocone-mediating morphism. -/
theorem mediatingSup_mediates
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (hF : IsDcpo F)
    (hFanti : ∀ x y : F, x ≤ y → y ≤ x → x = y)
    (C' : ExpandingSequence.Cocone S F) :
    ExpandingSequence.CoconeMediates S C C' (h.mediatingSup hantisymm hF C') := by
  exact ⟨h.mediatingSup_scottContinuous hantisymm hF C',
    h.mediatingSup_commute hantisymm hF hFanti C'⟩

/-- Any cocone-mediating map out of a decomposed cocone agrees with the canonical
supremum map. -/
theorem mediatingSup_unique
    (h : ExpandingSequence.CoconeEPDecomposition S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {F : Type u} [Preorder F] (hF : IsDcpo F)
    (hFanti : ∀ x y : F, x ≤ y → y ≤ x → x = y)
    (C' : ExpandingSequence.Cocone S F)
    (v : E → F) (hv : ExpandingSequence.CoconeMediates S C C' v) :
    ∀ y : E, v y = h.mediatingSup hantisymm hF C' y := by
  intro y
  have hsourceSup : IsSup (h.SourceImage y) y := by
    simpa [SourceImage] using h.sup_identity y
  have hvSourceSup : IsSup (v '' h.SourceImage y) (v y) :=
    hv.1.2 (h.sourceImage_directed hantisymm y) hsourceSup
  have hvTargetSup : IsSup (h.TargetImage C' y) (v y) := by
    constructor
    · intro z hz
      rcases hz with ⟨n, rfl⟩
      have hsrcMem : (h.ep n).e ((h.ep n).p y) ∈ h.SourceImage y := ⟨n, rfl⟩
      have hsrcLe : (h.ep n).e ((h.ep n).p y) ≤ y := hsourceSup.1 hsrcMem
      calc
        C'.f n ((h.ep n).p y)
            = v (C.f n ((h.ep n).p y)) := (hv.2 n ((h.ep n).p y)).symm
        _ = v ((h.ep n).e ((h.ep n).p y)) := by
            rw [(h.ep_e n ((h.ep n).p y)).symm]
        _ ≤ v y := hv.1.1 hsrcLe
    · intro b hb
      exact hvSourceSup.2 b (by
        intro w hw
        rcases hw with ⟨z, hz, rfl⟩
        rcases hz with ⟨n, rfl⟩
        calc
          v ((h.ep n).e ((h.ep n).p y))
              = v (C.f n ((h.ep n).p y)) := by
                  rw [h.ep_e n ((h.ep n).p y)]
          _ = C'.f n ((h.ep n).p y) := hv.2 n ((h.ep n).p y)
          _ ≤ b := hb ⟨n, rfl⟩)
  have hchosen := h.mediatingSup_isSup hantisymm hF C' y
  exact hFanti _ _
    (hvTargetSup.2 (h.mediatingSup hantisymm hF C' y) hchosen.1)
    (hchosen.2 (v y) hvTargetSup.1)

end ExpandingSequence.CoconeEPDecomposition

/-- Lemma 3.3.8 sufficiency direction: an e-p-pair decomposition with
`⋁_n f_n(g_n(y)) = y` makes the cocone colimiting. -/
theorem ExpandingSequence.isColimitingCocone_of_epDecomposition
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    {C : ExpandingSequence.Cocone S E}
    (h : ExpandingSequence.CoconeEPDecomposition S C) :
    ExpandingSequence.IsColimitingCocone S hE hEanti C := by
  intro F _ hF hFanti C'
  refine ⟨h.mediatingSup hantisymm hF C', ?_, ?_⟩
  · exact h.mediatingSup_mediates hantisymm hF hFanti C'
  · intro v hv y
    exact h.mediatingSup_unique hantisymm hF hFanti C' v hv y

/-- The image family `{f_n(p_n x) | n ∈ Nat}` whose directed supremum is the
mediating map from the bilimit to a cocone carrier in Theorem 3.3.7 and
Proposition 3.3.9. -/
def ExpandingSequence.BilimitToCoconeImage
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.Cocone S E)
    (x : Bilimit S) : Set E :=
  {z | ∃ n : Nat, z = C.f n (Bilimit.proj S n x)}

/-- The family `{f_n(p_n x)}` is directed.  This is the directedness calculation
used in the proof of Theorem 3.3.7 to define the mediating map
`⋁_n f_n(p_n x)`. -/
theorem ExpandingSequence.bilimitToCoconeImage_directed
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.Cocone S E)
    (x : Bilimit S) : DirectedSet (ExpandingSequence.BilimitToCoconeImage S C x) := by
  constructor
  · exact ⟨C.f 0 (Bilimit.proj S 0 x), ⟨0, rfl⟩⟩
  · intro a ha b hb
    rcases ha with ⟨n, rfl⟩
    rcases hb with ⟨m, rfl⟩
    let k : Nat := max n m
    refine ⟨C.f k (Bilimit.proj S k x), ⟨k, rfl⟩, ?_, ?_⟩
    · have hnk : n ≤ k := Nat.le_max_left n m
      calc
        C.f n (Bilimit.proj S n x)
            = C.f n (S.p hnk (Bilimit.proj S k x)) := by
                congr
                simpa [Bilimit.proj, k] using x.2 hnk
        _ = C.f k (S.e hnk (S.p hnk (Bilimit.proj S k x))) :=
                (C.commute hnk (S.p hnk (Bilimit.proj S k x))).symm
        _ ≤ C.f k (Bilimit.proj S k x) :=
                (C.continuous k).1 (S.below hnk (Bilimit.proj S k x))
    · have hmk : m ≤ k := Nat.le_max_right n m
      calc
        C.f m (Bilimit.proj S m x)
            = C.f m (S.p hmk (Bilimit.proj S k x)) := by
                congr
                simpa [Bilimit.proj, k] using x.2 hmk
        _ = C.f k (S.e hmk (S.p hmk (Bilimit.proj S k x))) :=
                (C.commute hmk (S.p hmk (Bilimit.proj S k x))).symm
        _ ≤ C.f k (Bilimit.proj S k x) :=
                (C.continuous k).1 (S.below hmk (Bilimit.proj S k x))

/-- The canonical mediating map `Bilimit S -> E`, defined pointwise as the
supremum `⋁_n f_n(p_n x)` when the cocone carrier is a dcpo. -/
noncomputable def ExpandingSequence.bilimitToCoconeSup
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (C : ExpandingSequence.Cocone S E) : Bilimit S → E :=
  fun x => Classical.choose (hE _ (ExpandingSequence.bilimitToCoconeImage_directed S C x))

/-- The canonical mediating map is indeed the supremum of the family
`{f_n(p_n x)}`. -/
theorem ExpandingSequence.bilimitToCoconeSup_isSup
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (C : ExpandingSequence.Cocone S E) (x : Bilimit S) :
    IsSup (ExpandingSequence.BilimitToCoconeImage S C x)
      (ExpandingSequence.bilimitToCoconeSup S hE C x) :=
  Classical.choose_spec (hE _
    (ExpandingSequence.bilimitToCoconeImage_directed S C x))

/-- Each stage component `f_n(p_n x)` lies below the canonical supremum
`⋁_n f_n(p_n x)`. -/
theorem ExpandingSequence.bilimitToCocone_le_sup
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (C : ExpandingSequence.Cocone S E) (x : Bilimit S) (n : Nat) :
    C.f n (Bilimit.proj S n x) ≤ ExpandingSequence.bilimitToCoconeSup S hE C x :=
  (ExpandingSequence.bilimitToCoconeSup_isSup S hE C x).1 ⟨n, rfl⟩

/-- The canonical supremum map is monotone in the explicit bilimit order. -/
theorem ExpandingSequence.bilimitToCoconeSup_monotone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (C : ExpandingSequence.Cocone S E) :
    Monotone (ExpandingSequence.bilimitToCoconeSup S hE C) := by
  intro x y hxy
  exact (ExpandingSequence.bilimitToCoconeSup_isSup S hE C x).2
    (ExpandingSequence.bilimitToCoconeSup S hE C y) (by
      intro z hz
      rcases hz with ⟨n, rfl⟩
      calc
        C.f n (Bilimit.proj S n x)
            ≤ C.f n (Bilimit.proj S n y) := (C.continuous n).1 (hxy n)
        _ ≤ ExpandingSequence.bilimitToCoconeSup S hE C y :=
            ExpandingSequence.bilimitToCocone_le_sup S hE C y n)

/-- For an embedding cocone, the canonical supremum map satisfies the
`e ∘ p ≤ id` half of the e-p-pair laws. -/
theorem ExpandingSequence.bilimitToCoconeSup_below_of_embeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    {C : ExpandingSequence.Cocone S E}
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (y : E) :
    ExpandingSequence.bilimitToCoconeSup S hE C
        (hC.toBilimitOfAntisymm hantisymm y) ≤ y := by
  have hsup := ExpandingSequence.bilimitToCoconeSup_isSup S hE C
    (hC.toBilimitOfAntisymm hantisymm y)
  exact hsup.2 y (by
    intro z hz
    rcases hz with ⟨n, rfl⟩
    have hbelow : C.f n ((hC.ep n).p y) ≤ y := by
      calc
        C.f n ((hC.ep n).p y)
            = (hC.ep n).e ((hC.ep n).p y) := (hC.ep_e n _).symm
        _ ≤ y := (hC.ep n).below y
    simpa [Bilimit.proj, ExpandingSequence.CoconeEmbeddingData.toBilimitOfAntisymm]
      using hbelow)

/-- One half of the retract equation in Proposition 3.3.9: every bilimit point is
below the projection of its canonical image in the cocone carrier.  The reverse
inequality is the remaining nontrivial part of the retract proof. -/
theorem ExpandingSequence.le_toBilimitOf_bilimitToCoconeSup_of_embeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    {C : ExpandingSequence.Cocone S E}
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (x : Bilimit S) :
    x ≤ hC.toBilimitOfAntisymm hantisymm
      (ExpandingSequence.bilimitToCoconeSup S hE C x) := by
  intro n
  apply ((hC.ep n).toAdjunction.adj (Bilimit.proj S n x)
    (ExpandingSequence.bilimitToCoconeSup S hE C x)).2
  calc
    (hC.ep n).e (Bilimit.proj S n x)
        = C.f n (Bilimit.proj S n x) := hC.ep_e n _
    _ ≤ ExpandingSequence.bilimitToCoconeSup S hE C x :=
        ExpandingSequence.bilimitToCocone_le_sup S hE C x n

/-- Each stage image `f_m(x_m)` of a bilimit point projects below the `n`-th
coordinate of that point through the e-p-pair projection attached to the
embedding cocone. -/
theorem ExpandingSequence.coconeProjection_stage_le_of_embeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E]
    {C : ExpandingSequence.Cocone S E}
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (x : Bilimit S) (n m : Nat) :
    (hC.ep n).p (C.f m (Bilimit.proj S m x)) ≤ Bilimit.proj S n x := by
  rcases Nat.le_total n m with hnm | hmn
  · have hcoord :=
      hC.projection_commute_of_antisymm hantisymm hnm
        (C.f m (Bilimit.proj S m x))
    calc
      (hC.ep n).p (C.f m (Bilimit.proj S m x))
          = S.p hnm ((hC.ep m).p (C.f m (Bilimit.proj S m x))) := hcoord
      _ = S.p hnm ((hC.ep m).p ((hC.ep m).e (Bilimit.proj S m x))) := by
          rw [(hC.ep_e m (Bilimit.proj S m x)).symm]
      _ = S.p hnm (Bilimit.proj S m x) := by
          rw [(hC.ep m).retract]
      _ = Bilimit.proj S n x := by
          simpa [Bilimit.proj] using (x.2 hnm).symm
      _ ≤ Bilimit.proj S n x := le_rfl
  · have hcomm :
        C.f m (Bilimit.proj S m x) =
          C.f n (S.e hmn (Bilimit.proj S m x)) :=
      (C.commute hmn (Bilimit.proj S m x)).symm
    calc
      (hC.ep n).p (C.f m (Bilimit.proj S m x))
          = (hC.ep n).p (C.f n (S.e hmn (Bilimit.proj S m x))) := by
              rw [hcomm]
      _ = (hC.ep n).p ((hC.ep n).e (S.e hmn (Bilimit.proj S m x))) := by
              rw [(hC.ep_e n (S.e hmn (Bilimit.proj S m x))).symm]
      _ = S.e hmn (Bilimit.proj S m x) := by
              rw [(hC.ep n).retract]
      _ = S.e hmn (S.p hmn (Bilimit.proj S n x)) := by
              congr
              simpa [Bilimit.proj] using x.2 hmn
      _ ≤ Bilimit.proj S n x := S.below hmn (Bilimit.proj S n x)

/-- The reverse half of the retract equation for Proposition 3.3.9: projecting
the canonical supremum map back into the bilimit lies below the original
bilimit point. -/
theorem ExpandingSequence.toBilimitOf_bilimitToCoconeSup_le_of_embeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    {C : ExpandingSequence.Cocone S E}
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (x : Bilimit S) :
    hC.toBilimitOfAntisymm hantisymm
      (ExpandingSequence.bilimitToCoconeSup S hE C x) ≤ x := by
  intro n
  have hprojSup :
      IsSup ((hC.ep n).p '' ExpandingSequence.BilimitToCoconeImage S C x)
        ((hC.ep n).p (ExpandingSequence.bilimitToCoconeSup S hE C x)) :=
    ((hC.ep n).continuous_p).2
      (ExpandingSequence.bilimitToCoconeImage_directed S C x)
      (ExpandingSequence.bilimitToCoconeSup_isSup S hE C x)
  exact hprojSup.2 (Bilimit.proj S n x) (by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    rcases hy with ⟨m, rfl⟩
    exact ExpandingSequence.coconeProjection_stage_le_of_embeddingData
      S hC hantisymm x n m)

/-- The canonical supremum map in Proposition 3.3.9 is Scott-continuous for an
embedding cocone.  The key upper-bound argument sends an upper bound `b` of the
images of a directed family to the bilimit point `p(b)`, then uses the supremum
property in the bilimit order and the e-p-pair adjunctions stagewise. -/
theorem ExpandingSequence.bilimitToCoconeSup_scottContinuous_of_embeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    {C : ExpandingSequence.Cocone S E}
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ScottContinuous (ExpandingSequence.bilimitToCoconeSup S hE C) := by
  constructor
  · exact ExpandingSequence.bilimitToCoconeSup_monotone S hE C
  · intro A x hA hx
    constructor
    · intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact (ExpandingSequence.bilimitToCoconeSup_monotone S hE C) (hx.1 ha)
    · intro b hb
      have hbproj : IsUpperBound A (hC.toBilimitOfAntisymm hantisymm b) := by
        intro a ha n
        apply ((hC.ep n).toAdjunction.adj (Bilimit.proj S n a) b).2
        calc
          (hC.ep n).e (Bilimit.proj S n a)
              = C.f n (Bilimit.proj S n a) := hC.ep_e n _
          _ ≤ ExpandingSequence.bilimitToCoconeSup S hE C a :=
              ExpandingSequence.bilimitToCocone_le_sup S hE C a n
          _ ≤ b := hb ⟨a, ha, rfl⟩
      have hxproj : x ≤ hC.toBilimitOfAntisymm hantisymm b :=
        hx.2 (hC.toBilimitOfAntisymm hantisymm b) hbproj
      exact (ExpandingSequence.bilimitToCoconeSup_isSup S hE C x).2 b (by
        intro z hz
        rcases hz with ⟨n, rfl⟩
        have hnle : Bilimit.proj S n x ≤ (hC.ep n).p b := by
          simpa [Bilimit.proj, ExpandingSequence.CoconeEmbeddingData.toBilimitOfAntisymm]
            using hxproj n
        calc
          C.f n (Bilimit.proj S n x)
              = (hC.ep n).e (Bilimit.proj S n x) := (hC.ep_e n _).symm
          _ ≤ b := ((hC.ep n).toAdjunction.adj (Bilimit.proj S n x) b).1 hnle)

/-- Construction data for the embedding map `Bilimit S -> E` in Proposition
3.3.9.  The field `isSup_image` records the book's formula
`x ↦ ⋁_n f_n(p_n x)`, while the remaining fields are exactly the e-p-pair laws
with the projection map already constructed from the embedding cocone. -/
structure ExpandingSequence.BilimitToCoconeEmbeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.Cocone S E)
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) where
  toFun : Bilimit S → E
  continuous_toFun : ScottContinuous toFun
  isSup_image : (∀ x : Bilimit S,
    IsSup (ExpandingSequence.BilimitToCoconeImage S C x) (toFun x))
  retract_toBilimit : ∀ x : Bilimit S, hC.toBilimitOfAntisymm hantisymm (toFun x) = x
  below_toFun : ∀ y : E, toFun (hC.toBilimitOfAntisymm hantisymm y) ≤ y

/-- Proposition 3.3.9 support: a direct version of the previous packaging lemma
where the only supplied canonical-map obligation is Scott continuity. -/
noncomputable def ExpandingSequence.bilimitToCoconeEmbeddingData_of_continuousSup
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    {C : ExpandingSequence.Cocone S E}
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (hcont : ScottContinuous (ExpandingSequence.bilimitToCoconeSup S hE C)) :
    ExpandingSequence.BilimitToCoconeEmbeddingData S C hC hantisymm := by
  refine
    { toFun := ExpandingSequence.bilimitToCoconeSup S hE C
      continuous_toFun := hcont
      isSup_image := ExpandingSequence.bilimitToCoconeSup_isSup S hE C
      retract_toBilimit := ?_
      below_toFun :=
        ExpandingSequence.bilimitToCoconeSup_below_of_embeddingData S hE hC
          hantisymm }
  intro x
  apply Subtype.ext
  funext n
  exact hantisymm n _ _
    ((ExpandingSequence.toBilimitOf_bilimitToCoconeSup_le_of_embeddingData
      S hE hC hantisymm x) n)
    (ExpandingSequence.le_toBilimitOf_bilimitToCoconeSup_of_embeddingData
      S hE hC hantisymm x n)

/-- Proposition 3.3.9 support: the canonical supremum map supplies the full
embedding data for any embedding cocone over a dcpo carrier, under explicit
stage-order antisymmetry. -/
noncomputable def ExpandingSequence.bilimitToCoconeEmbeddingData_canonical
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    {C : ExpandingSequence.Cocone S E}
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.BilimitToCoconeEmbeddingData S C hC hantisymm :=
  ExpandingSequence.bilimitToCoconeEmbeddingData_of_continuousSup
    S hE hC hantisymm
    (ExpandingSequence.bilimitToCoconeSup_scottContinuous_of_embeddingData
      S hE hC hantisymm)

/-- The bilimit is a sub-domain of `E`, represented by an embedding-projection
pair from the bilimit into `E`. -/
def ExpandingSequence.BilimitSubdomainOf
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (E : Type u) [Preorder E] : Prop :=
  Nonempty (EPPair (Bilimit S) E)

/-- Proposition 3.3.9 support: once the canonical supremum map from the bilimit
to the cocone carrier is available with the book's two e-p-pair laws, it packages
with `toBilimitOfAntisymm` to make the bilimit a sub-domain of the cocone
carrier. -/
theorem ExpandingSequence.bilimitSubdomainOf_of_embeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.Cocone S E)
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (hmap : ExpandingSequence.BilimitToCoconeEmbeddingData S C hC hantisymm) :
    ExpandingSequence.BilimitSubdomainOf S E := by
  exact ⟨{
    e := hmap.toFun
    p := hC.toBilimitOfAntisymm hantisymm
    continuous_e := hmap.continuous_toFun
    continuous_p := hC.toBilimitOfAntisymm_scottContinuous hantisymm
    retract := hmap.retract_toBilimit
    below := hmap.below_toFun
  }⟩

/-- Proposition 3.3.9 support: the canonical supremum construction makes the
bilimit a sub-domain of the cocone carrier whenever the carrier is a dcpo and
the stage preorders are explicitly antisymmetric. -/
theorem ExpandingSequence.bilimitSubdomainOf_of_embeddingData_canonical
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (C : ExpandingSequence.Cocone S E)
    (hC : ExpandingSequence.CoconeEmbeddingData S C)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.BilimitSubdomainOf S E := by
  exact ExpandingSequence.bilimitSubdomainOf_of_embeddingData S C hC hantisymm
    (ExpandingSequence.bilimitToCoconeEmbeddingData_canonical S hE hC hantisymm)

/-- The explicit bilimit preorder is antisymmetric whenever all stage preorders
are antisymmetric.  This is the poset component needed by the restricted-DCPO
form of Corollary 3.3.10. -/
theorem ExpandingSequence.bilimit_antisymm_of_stage_antisymm
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ∀ x y : Bilimit S, x ≤ y → y ≤ x → x = y := by
  intro x y hxy hyx
  apply Subtype.ext
  funext n
  exact hantisymm n _ _ (hxy n) (hyx n)

/-- The explicit bilimit carrier is a dcpo whenever all stage carriers are dcpos
and their preorders are antisymmetric.  Directed suprema are computed
coordinatewise, and compatibility follows by applying the continuous projections
`p_{n,m}` to the coordinate suprema. -/
theorem ExpandingSequence.bilimit_dcpo_of_stage_dcpo
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    IsDcpo (Bilimit S) := by
  intro A hA
  let coordSet : ∀ n : Nat, Set (D n) :=
    fun n => (fun x : Bilimit S => Bilimit.proj S n x) '' A
  have hcoordDir : ∀ n : Nat, DirectedSet (coordSet n) := by
    intro n
    exact DirectedSet.image
      (fun (x y : Bilimit S) (hxy : x ≤ y) => by
        change x.1 n ≤ y.1 n
        change (∀ n : Nat, x.1 n ≤ y.1 n) at hxy
        exact hxy n) hA
  let coordSup : ∀ n : Nat, D n :=
    fun n => Classical.choose (hDdcpo n (coordSet n) (hcoordDir n))
  have hcoordSup : ∀ n : Nat, IsSup (coordSet n) (coordSup n) := by
    intro n
    exact Classical.choose_spec (hDdcpo n (coordSet n) (hcoordDir n))
  have hcarrier : BilimitCarrier S coordSup := by
    intro n m hnm
    apply hantisymm n
    · exact (hcoordSup n).2 (S.p hnm (coordSup m)) (by
        intro y hy
        rcases hy with ⟨a, ha, rfl⟩
        calc
          Bilimit.proj S n a = S.p hnm (Bilimit.proj S m a) := by
              simpa [Bilimit.proj] using a.2 hnm
          _ ≤ S.p hnm (coordSup m) :=
              (S.continuous_p hnm).1 ((hcoordSup m).1 ⟨a, ha, rfl⟩))
    · have hprojSup :
          IsSup ((S.p hnm) '' coordSet m) (S.p hnm (coordSup m)) :=
        (S.continuous_p hnm).2 (hcoordDir m) (hcoordSup m)
      exact hprojSup.2 (coordSup n) (by
        intro y hy
        rcases hy with ⟨ym, hym, rfl⟩
        rcases hym with ⟨a, ha, rfl⟩
        calc
          S.p hnm (Bilimit.proj S m a) = Bilimit.proj S n a := by
              simpa [Bilimit.proj] using (a.2 hnm).symm
          _ ≤ coordSup n := (hcoordSup n).1 ⟨a, ha, rfl⟩)
  refine ⟨⟨coordSup, hcarrier⟩, ?_⟩
  constructor
  · intro a ha n
    exact (hcoordSup n).1 ⟨a, ha, rfl⟩
  · intro b hb n
    exact (hcoordSup n).2 (Bilimit.proj S n b) (by
      intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      exact hb ha n)

/-- Under stage dcpo/poset hypotheses, the canonical projections
`Bilimit S -> D_n` are Scott-continuous.  The proof compares an arbitrary
directed supremum in the bilimit with the coordinatewise supremum used in
`bilimit_dcpo_of_stage_dcpo`. -/
theorem ExpandingSequence.bilimitProj_scottContinuous_of_stage_dcpo
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (n : Nat) : ScottContinuous (Bilimit.proj S n) := by
  constructor
  · intro x y hxy
    change x.1 n ≤ y.1 n
    change (∀ n : Nat, x.1 n ≤ y.1 n) at hxy
    exact hxy n
  · intro A x hA hx
    let coordSet : ∀ n : Nat, Set (D n) :=
      fun n => (fun x : Bilimit S => Bilimit.proj S n x) '' A
    have hcoordDir : ∀ n : Nat, DirectedSet (coordSet n) := by
      intro n
      exact DirectedSet.image
        (fun (x y : Bilimit S) (hxy : x ≤ y) => by
          change x.1 n ≤ y.1 n
          change (∀ n : Nat, x.1 n ≤ y.1 n) at hxy
          exact hxy n) hA
    let coordSup : ∀ n : Nat, D n :=
      fun n => Classical.choose (hDdcpo n (coordSet n) (hcoordDir n))
    have hcoordSup : ∀ n : Nat, IsSup (coordSet n) (coordSup n) := by
      intro n
      exact Classical.choose_spec (hDdcpo n (coordSet n) (hcoordDir n))
    have hcarrier : BilimitCarrier S coordSup := by
      intro i j hij
      apply hantisymm i
      · exact (hcoordSup i).2 (S.p hij (coordSup j)) (by
          intro y hy
          rcases hy with ⟨a, ha, rfl⟩
          calc
            Bilimit.proj S i a = S.p hij (Bilimit.proj S j a) := by
                simpa [Bilimit.proj] using a.2 hij
            _ ≤ S.p hij (coordSup j) :=
                (S.continuous_p hij).1 ((hcoordSup j).1 ⟨a, ha, rfl⟩))
      · have hprojSup :
            IsSup ((S.p hij) '' coordSet j) (S.p hij (coordSup j)) :=
          (S.continuous_p hij).2 (hcoordDir j) (hcoordSup j)
        exact hprojSup.2 (coordSup i) (by
          intro y hy
          rcases hy with ⟨yj, hyj, rfl⟩
          rcases hyj with ⟨a, ha, rfl⟩
          calc
            S.p hij (Bilimit.proj S j a) = Bilimit.proj S i a := by
                simpa [Bilimit.proj] using (a.2 hij).symm
            _ ≤ coordSup i := (hcoordSup i).1 ⟨a, ha, rfl⟩)
    let y : Bilimit S := ⟨coordSup, hcarrier⟩
    have hy : IsSup A y := by
      constructor
      · intro a ha i
        exact (hcoordSup i).1 ⟨a, ha, rfl⟩
      · intro b hb i
        exact (hcoordSup i).2 (Bilimit.proj S i b) (by
          intro z hz
          rcases hz with ⟨a, ha, rfl⟩
          exact hb ha i)
    have hxy : x = y := by
      exact ExpandingSequence.bilimit_antisymm_of_stage_antisymm S hantisymm
        x y (hx.2 y hy.1) (hy.2 x hx.1)
    have hn : Bilimit.proj S n x = coordSup n := by
      rw [hxy]
      rfl
    rw [hn]
    simpa [coordSet, Bilimit.proj] using hcoordSup n

/-- The canonical projection cone of the explicit bilimit, available once the
stage dcpo/poset hypotheses make the coordinate projections Scott-continuous. -/
noncomputable def ExpandingSequence.bilimitProjectionCone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.ProjectionCone S (Bilimit S) where
  p := Bilimit.proj S
  continuous := ExpandingSequence.bilimitProj_scottContinuous_of_stage_dcpo S hDdcpo hantisymm
  commute := by
    intro n m h x
    simpa [Bilimit.proj] using (x.2 h).symm

/-- The mediating map from a projection cone to the explicit bilimit is the
tuple of its projection components, as stated in Theorem 3.3.7. -/
def ExpandingSequence.projectionConeToBilimit
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.ProjectionCone S E) :
    E → Bilimit S :=
  fun x => ⟨fun n => C.p n x, by
    intro n m h
    exact (C.commute h x).symm⟩

/-- The projection-cone mediating map into the explicit bilimit is
Scott-continuous because each coordinate projection is Scott-continuous and the
bilimit order is coordinatewise. -/
theorem ExpandingSequence.projectionConeToBilimit_scottContinuous
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    {E : Type u} [Preorder E] (C : ExpandingSequence.ProjectionCone S E) :
    ScottContinuous (ExpandingSequence.projectionConeToBilimit S C) := by
  constructor
  · intro x y hxy n
    exact (C.continuous n).1 hxy
  · intro A x hA hx
    constructor
    · intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      intro n
      exact ((C.continuous n).2 hA hx).1 ⟨a, ha, rfl⟩
    · intro b hb n
      exact ((C.continuous n).2 hA hx).2 (Bilimit.proj S n b) (by
        intro z hz
        rcases hz with ⟨a, ha, rfl⟩
        exact hb ⟨a, ha, rfl⟩ n)

/-- The canonical projection cone satisfies the ordinary DCPO limiting universal
property from Theorem 3.3.7.  This is the projection-side component needed before
the stronger restricted projection-category statement of Corollary 3.3.10 can be
closed. -/
theorem ExpandingSequence.isLimitingProjectionCone_bilimitProjectionCone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.IsLimitingProjectionCone S
      (ExpandingSequence.bilimit_dcpo_of_stage_dcpo S hDdcpo hantisymm)
      (ExpandingSequence.bilimit_antisymm_of_stage_antisymm S hantisymm)
      (ExpandingSequence.bilimitProjectionCone S hDdcpo hantisymm) := by
  intro F _ _hF _hFanti C'
  refine ⟨ExpandingSequence.projectionConeToBilimit S C', ?_, ?_⟩
  · constructor
    · exact ExpandingSequence.projectionConeToBilimit_scottContinuous S C'
    · intro n x
      rfl
  · intro v hv x
    apply Subtype.ext
    funext n
    exact hv.2 n x

/-- Projection maps in an expanding sequence compose as `p_nm ∘ p_mk = p_nk`.
The definition records only the corresponding embedding composition; this lemma
derives the projection law from the e-p-pair adjunctions and explicit
antisymmetry of the stage orders, matching the note after Definition 3.3.6. -/
theorem ExpandingSequence.projection_comp_of_antisymm
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {n m k : Nat} (hnm : n ≤ m) (hmk : m ≤ k) (hnk : n ≤ k) (z : D k) :
    S.p hnm (S.p hmk z) = S.p hnk z := by
  apply hantisymm n
  · apply ((S.epPair hnk).toAdjunction.adj (S.p hnm (S.p hmk z)) z).2
    calc
      S.e hnk (S.p hnm (S.p hmk z))
          = S.e hmk (S.e hnm (S.p hnm (S.p hmk z))) :=
              S.comp_e hnm hmk hnk _
      _ ≤ S.e hmk (S.p hmk z) :=
          (S.continuous_e hmk).1 (S.below hnm (S.p hmk z))
      _ ≤ z := S.below hmk z
  · apply ((S.epPair hnm).toAdjunction.adj (S.p hnk z) (S.p hmk z)).2
    apply ((S.epPair hmk).toAdjunction.adj (S.e hnm (S.p hnk z)) z).2
    calc
      S.e hmk (S.e hnm (S.p hnk z))
          = S.e hnk (S.p hnk z) := (S.comp_e hnm hmk hnk _).symm
      _ ≤ z := S.below hnk z

/-- Coordinate formula for the stage embedding `D_n -> Bilimit S`.  At
coordinate `i`, the PDF allows any common upper bound of `{i,n}`; here we use
`max i n` and take `p_{i,max i n} (e_{n,max i n} x)`. -/
def ExpandingSequence.stageProjectionMap
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (n i : Nat) : D n → D i :=
  fun x => S.p (Nat.le_max_left i n) (S.e (Nat.le_max_right i n) x)

/-- The coordinate maps used for a fixed stage form a projection cone over the
dual projection diagram. -/
theorem ExpandingSequence.stageProjectionMap_commute
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {i j : Nat} (hij : i ≤ j) (n : Nat) (x : D n) :
    S.p hij (S.stageProjectionMap n j x) = S.stageProjectionMap n i x := by
  let k₁ : Nat := max i n
  let k₂ : Nat := max j n
  have hik₁ : i ≤ k₁ := Nat.le_max_left i n
  have hnk₁ : n ≤ k₁ := Nat.le_max_right i n
  have hjk₂ : j ≤ k₂ := Nat.le_max_left j n
  have hnk₂ : n ≤ k₂ := Nat.le_max_right j n
  have hik₂ : i ≤ k₂ := le_trans hij hjk₂
  have hk₁k₂ : k₁ ≤ k₂ := (Nat.max_le).2 ⟨hik₂, hnk₂⟩
  have hpk :
      S.p hk₁k₂ (S.e hnk₂ x) = S.e hnk₁ x := by
    calc
      S.p hk₁k₂ (S.e hnk₂ x)
          = S.p hk₁k₂ (S.e hk₁k₂ (S.e hnk₁ x)) := by
              rw [(S.comp_e hnk₁ hk₁k₂ hnk₂ x)]
      _ = S.e hnk₁ x := S.retract hk₁k₂ (S.e hnk₁ x)
  calc
    S.p hij (S.stageProjectionMap n j x)
        = S.p hij (S.p hjk₂ (S.e hnk₂ x)) := rfl
    _ = S.p hik₂ (S.e hnk₂ x) :=
        S.projection_comp_of_antisymm hantisymm hij hjk₂ hik₂ (S.e hnk₂ x)
    _ = S.p hik₁ (S.p hk₁k₂ (S.e hnk₂ x)) :=
        (S.projection_comp_of_antisymm hantisymm hik₁ hk₁k₂ hik₂
          (S.e hnk₂ x)).symm
    _ = S.stageProjectionMap n i x := by
        rw [hpk]
        rfl

/-- The projection cone with carrier `D_n` whose components are the coordinate
maps of the stage embedding into the bilimit. -/
noncomputable def ExpandingSequence.stageProjectionCone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (n : Nat) : ExpandingSequence.ProjectionCone S (D n) where
  p := S.stageProjectionMap n
  continuous := fun i => by
    unfold ExpandingSequence.stageProjectionMap
    exact ScottContinuous.comp (S.continuous_p (Nat.le_max_left i n))
      (S.continuous_e (Nat.le_max_right i n))
  commute := by
    intro i j hij x
    exact S.stageProjectionMap_commute hantisymm hij n x

/-- The stage embedding `D_n -> Bilimit S`, implemented as the mediating map
from the stage projection cone. -/
noncomputable def ExpandingSequence.stageEmbedding
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (n : Nat) : D n → Bilimit S :=
  ExpandingSequence.projectionConeToBilimit S (S.stageProjectionCone hantisymm n)

/-- Coordinate equation for the stage embedding, using the `max` common upper
bound formula from `stageProjectionMap`. -/
theorem ExpandingSequence.stageEmbedding_proj
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (n i : Nat) (x : D n) :
    Bilimit.proj S i (S.stageEmbedding hantisymm n x) = S.stageProjectionMap n i x := by
  rfl

/-- The stage embedding is Scott-continuous because it is the mediating map from
a projection cone whose coordinate maps are Scott-continuous. -/
theorem ExpandingSequence.stageEmbedding_scottContinuous
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (n : Nat) : ScottContinuous (S.stageEmbedding hantisymm n) := by
  exact ExpandingSequence.projectionConeToBilimit_scottContinuous S
    (S.stageProjectionCone hantisymm n)

/-- The stage embedding and the canonical projection form the e-p-pair
`(e_n,p_n)` from Theorem 3.3.7. -/
noncomputable def ExpandingSequence.stageEPPair
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (n : Nat) : EPPair (D n) (Bilimit S) where
  e := S.stageEmbedding hantisymm n
  p := Bilimit.proj S n
  continuous_e := S.stageEmbedding_scottContinuous hantisymm n
  continuous_p := S.bilimitProj_scottContinuous_of_stage_dcpo hDdcpo hantisymm n
  retract := by
    intro x
    have hproof :
        Nat.le_max_right n n = Nat.le_max_left n n := Subsingleton.elim _ _
    change S.stageProjectionMap n n x = x
    unfold ExpandingSequence.stageProjectionMap
    rw [hproof]
    exact S.retract (Nat.le_max_left n n) x
  below := by
    intro y i
    let k : Nat := max i n
    have hik : i ≤ k := Nat.le_max_left i n
    have hnk : n ≤ k := Nat.le_max_right i n
    calc
      Bilimit.proj S i (S.stageEmbedding hantisymm n (Bilimit.proj S n y))
          = S.stageProjectionMap n i (Bilimit.proj S n y) := rfl
      _ = S.p hik (S.e hnk (S.p hnk (Bilimit.proj S k y))) := by
          unfold ExpandingSequence.stageProjectionMap
          rw [show Bilimit.proj S n y = S.p hnk (Bilimit.proj S k y) by
            simpa [Bilimit.proj] using y.2 hnk]
      _ ≤ S.p hik (Bilimit.proj S k y) :=
          (S.continuous_p hik).1 (S.below hnk (Bilimit.proj S k y))
      _ = Bilimit.proj S i y := by
          simpa [Bilimit.proj] using (y.2 hik).symm

/-- The stage-embedding coordinate formula is compatible with the connecting
embeddings: the `m`-stage embedding after `e_{n,m}` has the same coordinates as
the `n`-stage embedding. -/
theorem ExpandingSequence.stageProjectionMap_of_embedding
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {n m : Nat} (hnm : n ≤ m) (i : Nat) (x : D n) :
    S.stageProjectionMap m i (S.e hnm x) = S.stageProjectionMap n i x := by
  let k₁ : Nat := max i n
  let k₂ : Nat := max i m
  have hik₁ : i ≤ k₁ := Nat.le_max_left i n
  have hnk₁ : n ≤ k₁ := Nat.le_max_right i n
  have hik₂ : i ≤ k₂ := Nat.le_max_left i m
  have hmk₂ : m ≤ k₂ := Nat.le_max_right i m
  have hnk₂ : n ≤ k₂ := le_trans hnm hmk₂
  have hk₁k₂ : k₁ ≤ k₂ := (Nat.max_le).2 ⟨hik₂, hnk₂⟩
  have hpk : S.p hk₁k₂ (S.e hnk₂ x) = S.e hnk₁ x := by
    calc
      S.p hk₁k₂ (S.e hnk₂ x)
          = S.p hk₁k₂ (S.e hk₁k₂ (S.e hnk₁ x)) := by
              rw [S.comp_e hnk₁ hk₁k₂ hnk₂ x]
      _ = S.e hnk₁ x := S.retract hk₁k₂ (S.e hnk₁ x)
  calc
    S.stageProjectionMap m i (S.e hnm x)
        = S.p hik₂ (S.e hmk₂ (S.e hnm x)) := rfl
    _ = S.p hik₂ (S.e hnk₂ x) := by
        rw [(S.comp_e hnm hmk₂ hnk₂ x).symm]
    _ = S.p hik₁ (S.p hk₁k₂ (S.e hnk₂ x)) :=
        (S.projection_comp_of_antisymm hantisymm hik₁ hk₁k₂ hik₂
          (S.e hnk₂ x)).symm
    _ = S.stageProjectionMap n i x := by
        rw [hpk]
        rfl

/-- The stage embeddings commute with the expanding-sequence embeddings, giving
the canonical embedding cocone over the explicit bilimit. -/
theorem ExpandingSequence.stageEmbedding_commute
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {n m : Nat} (hnm : n ≤ m) (x : D n) :
    S.stageEmbedding hantisymm m (S.e hnm x) = S.stageEmbedding hantisymm n x := by
  apply Subtype.ext
  funext i
  exact S.stageProjectionMap_of_embedding hantisymm hnm i x

/-- The canonical embedding cocone of the explicit bilimit, with legs the stage
embeddings from Theorem 3.3.7. -/
noncomputable def ExpandingSequence.bilimitEmbeddingCocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.Cocone S (Bilimit S) where
  f := S.stageEmbedding hantisymm
  continuous := S.stageEmbedding_scottContinuous hantisymm
  commute := by
    intro n m h x
    exact S.stageEmbedding_commute hantisymm h x

/-- The canonical embedding cocone has embedding data: its legs are the
embedding halves of the e-p-pairs `(e_n,p_n)` from Theorem 3.3.7. -/
noncomputable def ExpandingSequence.bilimitEmbeddingCoconeEmbeddingData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.CoconeEmbeddingData S (S.bilimitEmbeddingCocone hantisymm) where
  ep := S.stageEPPair hDdcpo hantisymm
  ep_e := by
    intro n x
    rfl

/-- The canonical embedding cocone satisfies the e-p-pair decomposition
criterion from Lemma 3.3.8.  The supremum identity is the coordinatewise form of
`⋁_n e_n ∘ p_n = id_D` from Theorem 3.3.7. -/
noncomputable def ExpandingSequence.bilimitEmbeddingCoconeEPDecomposition
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.CoconeEPDecomposition S (S.bilimitEmbeddingCocone hantisymm) where
  ep := S.stageEPPair hDdcpo hantisymm
  ep_e := by
    intro n x
    rfl
  sup_identity := by
    intro y
    constructor
    · intro z hz
      rcases hz with ⟨n, rfl⟩
      exact (S.stageEPPair hDdcpo hantisymm n).below y
    · intro b hb i
      have hUpper :
          S.stageEmbedding hantisymm i (Bilimit.proj S i y) ≤ b := by
        exact hb ⟨i, rfl⟩
      calc
        Bilimit.proj S i y
            = Bilimit.proj S i (S.stageEmbedding hantisymm i (Bilimit.proj S i y)) :=
                ((S.stageEPPair hDdcpo hantisymm i).retract
                  (Bilimit.proj S i y)).symm
        _ ≤ Bilimit.proj S i b := hUpper i

/-- The canonical supremum map from the bilimit to an embedding cocone agrees
with the cocone leg on each stage embedding. -/
theorem ExpandingSequence.bilimitToCoconeSup_stageEmbedding
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    (C : ExpandingSequence.Cocone S E) (n : Nat) (x : D n) :
    ExpandingSequence.bilimitToCoconeSup S hE C (S.stageEmbedding hantisymm n x) =
      C.f n x := by
  let hB := S.bilimitEmbeddingCoconeEPDecomposition hDdcpo hantisymm
  have hchosen :=
    ExpandingSequence.bilimitToCoconeSup_isSup S hE C (S.stageEmbedding hantisymm n x)
  have hstage :
      IsSup (ExpandingSequence.BilimitToCoconeImage S C
        (S.stageEmbedding hantisymm n x)) (C.f n x) := by
    simpa [ExpandingSequence.BilimitToCoconeImage,
      ExpandingSequence.CoconeEPDecomposition.TargetImage,
      ExpandingSequence.bilimitEmbeddingCocone,
      ExpandingSequence.bilimitEmbeddingCoconeEPDecomposition,
      ExpandingSequence.stageEPPair] using
      (hB.targetImage_stage_isSup hantisymm C n x)
  exact hEanti _ _
    (hchosen.2 (C.f n x) hstage.1)
    (hstage.2 (ExpandingSequence.bilimitToCoconeSup S hE C
      (S.stageEmbedding hantisymm n x)) hchosen.1)

/-- The canonical supremum map from the bilimit to an embedding cocone is a
cocone-mediating map. -/
theorem ExpandingSequence.bilimitToCoconeSup_mediates_bilimitEmbeddingCocone
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {E : Type u} [Preorder E] (hE : IsDcpo E)
    (hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    {C : ExpandingSequence.Cocone S E}
    (hC : ExpandingSequence.CoconeEmbeddingData S C) :
    ExpandingSequence.CoconeMediates S (S.bilimitEmbeddingCocone hantisymm) C
      (ExpandingSequence.bilimitToCoconeSup S hE C) := by
  constructor
  · exact ExpandingSequence.bilimitToCoconeSup_scottContinuous_of_embeddingData
      S hE hC hantisymm
  · intro n x
    exact S.bilimitToCoconeSup_stageEmbedding hDdcpo hantisymm hE hEanti C n x

/-- Theorem 3.3.7 full data package.

PDF text excerpt: "Let `⟨(D_n)_{n∈N}, (e_mn : D_n → D_m)_{n≤m∈N}⟩` be an
expanding sequence in `DCPO`. Define an object `D` by compatible tuples
`x_n = p_nm(x_m)`, projections `p_m : D → D_m`, and embeddings
`e_m : D_m → D` by the coordinate formula using a common upper bound. Then:
(1) the maps `(e_m,p_m)` form embedding projection pairs and
`⋁_m e_m ∘ p_m = id_D`; (2) `⟨D,(p_n)⟩` is a limit of the projection diagram;
(3) `⟨D,(e_n)⟩` is a colimit of the embedding diagram."

Current Lean spelling: the theorem is packaged in the preorder interface under
explicit stage `IsDcpo` and antisymmetry hypotheses.  The fields below record
the dcpo/poset structure of the bilimit carrier, the projection-limit universal
property, the canonical e-p-pair decomposition, and the embedding-colimit
universal property. -/
structure ExpandingSequence.BilimitTheoremFullData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (_hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) where
  bilimit_dcpo : IsDcpo (Bilimit S)
  bilimit_antisymm : ∀ x y : Bilimit S, x ≤ y → y ≤ x → x = y
  projectionCone : ExpandingSequence.ProjectionCone S (Bilimit S)
  projectionCone_proj : ∀ n : Nat, ∀ x : Bilimit S, projectionCone.p n x = Bilimit.proj S n x
  limiting_projection :
    ExpandingSequence.IsLimitingProjectionCone S bilimit_dcpo bilimit_antisymm projectionCone
  embeddingCocone : ExpandingSequence.Cocone S (Bilimit S)
  embeddingCocone_f :
    ∀ n : Nat, ∀ x : D n, embeddingCocone.f n x = S.stageEmbedding hantisymm n x
  ep_decomposition : ExpandingSequence.CoconeEPDecomposition S embeddingCocone
  colimiting_embedding :
    ExpandingSequence.IsColimitingCocone S bilimit_dcpo bilimit_antisymm embeddingCocone

/-- Theorem 3.3.7, full preorder-interface form.

Current Lean spelling: construct the full package described above for an
expanding sequence once each stage is a dcpo and its preorder is explicitly
antisymmetric. -/
noncomputable def theorem_3_3_7_expanding_sequence_bilimit
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.BilimitTheoremFullData S hDdcpo hantisymm where
  bilimit_dcpo := S.bilimit_dcpo_of_stage_dcpo hDdcpo hantisymm
  bilimit_antisymm := S.bilimit_antisymm_of_stage_antisymm hantisymm
  projectionCone := S.bilimitProjectionCone hDdcpo hantisymm
  projectionCone_proj := by
    intro n x
    rfl
  limiting_projection :=
    S.isLimitingProjectionCone_bilimitProjectionCone hDdcpo hantisymm
  embeddingCocone := S.bilimitEmbeddingCocone hantisymm
  embeddingCocone_f := by
    intro n x
    rfl
  ep_decomposition :=
    S.bilimitEmbeddingCoconeEPDecomposition hDdcpo hantisymm
  colimiting_embedding :=
    S.isColimitingCocone_of_epDecomposition hantisymm
      (S.bilimit_dcpo_of_stage_dcpo hDdcpo hantisymm)
      (S.bilimit_antisymm_of_stage_antisymm hantisymm)
      (S.bilimitEmbeddingCoconeEPDecomposition hDdcpo hantisymm)

/-- Theorem 3.3.7, theorem-facing existence wrapper for the full bilimit
limit-colimit package. -/
theorem theorem_3_3_7_expanding_sequence_bilimit_exists
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    Nonempty (ExpandingSequence.BilimitTheoremFullData S hDdcpo hantisymm) :=
  ⟨theorem_3_3_7_expanding_sequence_bilimit S hDdcpo hantisymm⟩


end Chapter3
end AbramskyJung

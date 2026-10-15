import Practice.DomainTheory.Chapter03.NumberedItems.Section33_BilimitUniversal

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Chapter 3: Section 3.3 preservation by bilimits

Book-facing declarations and their local support API are kept together in
textbook dependency order. Reusable constructions remain in the concept-owned
`Chapter03.Section*` modules.
-/

universe u v w z l

namespace AbramskyJung
namespace Chapter3

/-- The stage-image union `⋃ n, e_n(B_n)` appearing in Theorem 3.3.11, with the
maps into the bilimit supplied explicitly by the theorem data. -/
def ExpandingSequence.BilimitBasisUnion
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (stageEmbed : ∀ n : Nat, D n → Bilimit S) (B : ∀ n : Nat, Set (D n)) :
    Set (Bilimit S) :=
  {x | ∃ n : Nat, ∃ b : D n, b ∈ B n ∧ x = stageEmbed n b}

/-- The compact-stage union `⋃ n, e_n(K(D_n))` from the algebraic part of
Theorem 3.3.11. -/
def ExpandingSequence.BilimitCompactUnion
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D)
    (stageEmbed : ∀ n : Nat, D n → Bilimit S) : Set (Bilimit S) :=
  ExpandingSequence.BilimitBasisUnion S stageEmbed
    (fun n : Nat => (Chapter2.CompactSet : Set (D n)))

/-- The canonical stage embedding sends stage approximants to bilimit
approximants.  This is the formal version of the proof step in Theorem 3.3.11
where the maps `e_n` are used as lower adjoints. -/
theorem ExpandingSequence.stageEmbedding_wayBelow_bilimit
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    {n : Nat} {b : D n} {x : Bilimit S}
    (hb : b ≪ Bilimit.proj S n x) :
    S.stageEmbedding hantisymm n b ≪ x := by
  exact Chapter2.prop_2_2_2_2 le_rfl
    ((S.stageEPPair hDdcpo hantisymm n).wayBelow_iff.2 hb)
    ((S.stageEPPair hDdcpo hantisymm n).below x)

/-- The basis-union clause in Theorem 3.3.11: if each stage has a basis `B n`,
then the union of the images of those bases under the canonical bilimit stage
embeddings is a basis for the bilimit. -/
theorem ExpandingSequence.bilimitBasisUnion_isBasisRaw
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (B : ∀ n : Nat, Set (D n)) (hB : ∀ n : Nat, Chapter2.IsBasisRaw (B n)) :
    Chapter2.IsBasisRaw
      (ExpandingSequence.BilimitBasisUnion S (S.stageEmbedding hantisymm) B) := by
  intro x
  let A : Set (Bilimit S) :=
    {z | ∃ n : Nat, ∃ b : D n,
      b ∈ Chapter2.Approximants (B n) (Bilimit.proj S n x) ∧
        z = S.stageEmbedding hantisymm n b}
  refine ⟨A, ?_, ?_, ?_⟩
  · intro z hz
    rcases hz with ⟨n, b, hb, rfl⟩
    constructor
    · exact ⟨n, b, hb.1, rfl⟩
    · exact S.stageEmbedding_wayBelow_bilimit hDdcpo hantisymm hb.2
  · constructor
    · rcases hB 0 (Bilimit.proj S 0 x) with ⟨A0, hA0sub, hA0dir, _hA0sup⟩
      rcases hA0dir.1 with ⟨b0, hb0⟩
      exact ⟨S.stageEmbedding hantisymm 0 b0, 0, b0, hA0sub hb0, rfl⟩
    · intro z hz w hw
      rcases hz with ⟨n, b, hb, rfl⟩
      rcases hw with ⟨m, c, hc, rfl⟩
      let k : Nat := max n m
      have hnk : n ≤ k := Nat.le_max_left n m
      have hmk : m ≤ k := Nat.le_max_right n m
      have hbLiftWay :
          S.e hnk b ≪ Bilimit.proj S k x := by
        have hbEmb :
            S.e hnk b ≪ S.e hnk (Bilimit.proj S n x) :=
          ((S.epPair hnk).wayBelow_iff).2 hb.2
        have hxnk : Bilimit.proj S n x = S.p hnk (Bilimit.proj S k x) := by
          simpa [Bilimit.proj] using x.2 hnk
        have hbTarget :
            S.e hnk (Bilimit.proj S n x) ≤ Bilimit.proj S k x := by
          rw [hxnk]
          exact S.below hnk (Bilimit.proj S k x)
        exact Chapter2.prop_2_2_2_2 le_rfl hbEmb hbTarget
      have hcLiftWay :
          S.e hmk c ≪ Bilimit.proj S k x := by
        have hcEmb :
            S.e hmk c ≪ S.e hmk (Bilimit.proj S m x) :=
          ((S.epPair hmk).wayBelow_iff).2 hc.2
        have hxmk : Bilimit.proj S m x = S.p hmk (Bilimit.proj S k x) := by
          simpa [Bilimit.proj] using x.2 hmk
        have hcTarget :
            S.e hmk (Bilimit.proj S m x) ≤ Bilimit.proj S k x := by
          rw [hxmk]
          exact S.below hmk (Bilimit.proj S k x)
        exact Chapter2.prop_2_2_2_2 le_rfl hcEmb hcTarget
      have hKbasis : Chapter2.IsBasis (B k) := Chapter2.prop_2_2_4_1 (hB k)
      have hKdir :
          DirectedSet (Chapter2.Approximants (B k) (Bilimit.proj S k x)) :=
        (hKbasis (Bilimit.proj S k x)).1
      have hKsup :
          IsSup (Chapter2.Approximants (B k) (Bilimit.proj S k x))
            (Bilimit.proj S k x) :=
        (hKbasis (Bilimit.proj S k x)).2
      rcases hbLiftWay hKdir hKsup le_rfl with ⟨b', hb'Mem, hbLe⟩
      rcases hcLiftWay hKdir hKsup le_rfl with ⟨c', hc'Mem, hcLe⟩
      rcases hKdir.2 hb'Mem hc'Mem with ⟨d, hdMem, hb'd, hc'd⟩
      refine ⟨S.stageEmbedding hantisymm k d, ?_, ?_, ?_⟩
      · exact ⟨k, d, hdMem, rfl⟩
      · calc
          S.stageEmbedding hantisymm n b
              = S.stageEmbedding hantisymm k (S.e hnk b) := by
                  exact (S.stageEmbedding_commute hantisymm hnk b).symm
          _ ≤ S.stageEmbedding hantisymm k d :=
              (S.stageEmbedding_scottContinuous hantisymm k).1 (le_trans hbLe hb'd)
      · calc
          S.stageEmbedding hantisymm m c
              = S.stageEmbedding hantisymm k (S.e hmk c) := by
                  exact (S.stageEmbedding_commute hantisymm hmk c).symm
          _ ≤ S.stageEmbedding hantisymm k d :=
              (S.stageEmbedding_scottContinuous hantisymm k).1 (le_trans hcLe hc'd)
  · constructor
    · intro z hz
      rcases hz with ⟨n, b, hb, rfl⟩
      have hbLe : b ≤ Bilimit.proj S n x := Chapter2.prop_2_2_2_1 hb.2
      calc
        S.stageEmbedding hantisymm n b
            ≤ S.stageEmbedding hantisymm n (Bilimit.proj S n x) :=
              (S.stageEmbedding_scottContinuous hantisymm n).1 hbLe
        _ ≤ x := (S.stageEPPair hDdcpo hantisymm n).below x
    · intro y hy i
      have hIbasis : Chapter2.IsBasis (B i) := Chapter2.prop_2_2_4_1 (hB i)
      exact ((hIbasis (Bilimit.proj S i x)).2).2 (Bilimit.proj S i y) (by
        intro b hb
        have hUpper :
            S.stageEmbedding hantisymm i b ≤ y :=
          hy ⟨i, b, hb, rfl⟩
        calc
          b = Bilimit.proj S i (S.stageEmbedding hantisymm i b) := by
                exact ((S.stageEPPair hDdcpo hantisymm i).retract b).symm
          _ ≤ Bilimit.proj S i y :=
                (S.bilimitProj_scottContinuous_of_stage_dcpo hDdcpo hantisymm i).1 hUpper)

/-- Countability of the stage-image union used in the omega clauses of Theorem
3.3.11. -/
theorem ExpandingSequence.bilimitBasisUnion_countable
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (B : ∀ n : Nat, Set (D n)) (hBcount : ∀ n : Nat, (B n).Countable) :
    (ExpandingSequence.BilimitBasisUnion S (S.stageEmbedding hantisymm) B).Countable := by
  refine Set.Countable.mono ?_
    (Set.countable_iUnion
      (fun n : Nat => Set.Countable.image (hBcount n) (S.stageEmbedding hantisymm n)))
  intro x hx
  rcases hx with ⟨n, b, hb, rfl⟩
  exact Set.mem_iUnion.2 ⟨n, b, hb, rfl⟩

/-- The compact-basis equality in Theorem 3.3.11: for an algebraic expanding
sequence, compact elements of the bilimit are exactly the images of compact
elements from finite stages. -/
theorem ExpandingSequence.bilimitCompactSet_eq
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (hAlg : ∀ n : Nat, IsAlgebraicDomain (D n)) :
    (Chapter2.CompactSet : Set (Bilimit S)) =
      ExpandingSequence.BilimitCompactUnion S (S.stageEmbedding hantisymm) := by
  ext x
  constructor
  · intro hxCompact
    have hBasisRaw :
        Chapter2.IsBasisRaw
          (ExpandingSequence.BilimitCompactUnion S (S.stageEmbedding hantisymm)) :=
      S.bilimitBasisUnion_isBasisRaw hDdcpo hantisymm
        (fun n : Nat => (Chapter2.CompactSet : Set (D n)))
        (fun n => Chapter2.basis_to_raw (hAlg n))
    rcases hBasisRaw x with ⟨A, hAsub, hAdir, hAsup⟩
    have hxWay : x ≪ x := by
      simpa [Chapter2.CompactSet, Chapter2.Compact] using hxCompact
    rcases hxWay hAdir hAsup le_rfl with ⟨a, ha, hxa⟩
    have haApprox := hAsub ha
    have hax : a ≤ x := Chapter2.prop_2_2_2_1 haApprox.2
    have hEq : x = a :=
      S.bilimit_antisymm_of_stage_antisymm hantisymm x a hxa hax
    simpa [hEq] using haApprox.1
  · intro hxUnion
    rcases hxUnion with ⟨n, c, hcCompact, rfl⟩
    have hcWay : c ≪ c := by
      simpa [Chapter2.CompactSet, Chapter2.Compact] using hcCompact
    have hProj :
        Bilimit.proj S n (S.stageEmbedding hantisymm n c) = c :=
      (S.stageEPPair hDdcpo hantisymm n).retract c
    have hcProjWay : c ≪ Bilimit.proj S n (S.stageEmbedding hantisymm n c) := by
      simpa [hProj] using hcWay
    exact S.stageEmbedding_wayBelow_bilimit hDdcpo hantisymm hcProjWay

/-- Bilimit preservation, continuous-domain component of Theorem 3.3.11.

Current Lean spelling: Chapter 3's `IsContinuousDomain` uses the strong basis
predicate `IsBasis`; the full theorem supplies the explicit stage dcpo and
antisymmetry hypotheses needed by the preorder interface. -/
def ExpandingSequence.BilimitPreservation
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)] (S : ExpandingSequence D) : Prop :=
  (∀ n : Nat, IsContinuousDomain (D n)) → IsContinuousDomain (Bilimit S)

/-- Theorem 3.3.11 full data package.

PDF text: "Let `⟨(D_n)_{n∈N}, (e_mn : D_n → D_m)_{n≤m∈N}⟩` be an expanding
sequence and `⟨D,(e_n)_{n∈N}⟩` its bilimit. (1) If all `D_n` are
`(ω-)continuous` then so is `D`. If we are given bases `B_n`, `n ∈ N`, for each
`D_n` then a basis for `D` is given by `⋃_{n∈N} e_n(B_n)`. (2) If all `D_n`
are `(ω-)algebraic` then so is `D` and `K(D) = ⋃_{n∈N} e_n(K(D_n))`."

Current Lean spelling: stage dcpo and stage antisymmetry hypotheses are explicit.
The continuous/algebraic fields use Chapter 3's strong basis predicates, while
the omega fields and the explicit basis-union clauses use the Chapter 2 raw
basis/countability predicates. -/
structure ExpandingSequence.BilimitPreservationData
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) where
  stageEmbed : ∀ n : Nat, D n → Bilimit S
  stageEmbed_continuous : ∀ n : Nat, ScottContinuous (stageEmbed n)
  stageEmbed_retract : ∀ n : Nat, ∀ x : D n, Bilimit.proj S n (stageEmbed n x) = x
  stageEmbed_below : ∀ n : Nat, ∀ y : Bilimit S, stageEmbed n (Bilimit.proj S n y) ≤ y
  stageEmbed_commute :
    ∀ {n m : Nat}, ∀ h : n ≤ m, ∀ x : D n, stageEmbed m (S.e h x) = stageEmbed n x
  continuous : (∀ n : Nat, IsContinuousDomain (D n)) → IsContinuousDomain (Bilimit S)
  omega_continuous :
    (∀ n : Nat, Chapter2.IsOmegaContinuousDomain (D n)) →
      Chapter2.IsOmegaContinuousDomain (Bilimit S)
  basis_union :
    ∀ B : ∀ n : Nat, Set (D n), (∀ n : Nat, Chapter2.IsBasisRaw (B n)) →
      Chapter2.IsBasisRaw (ExpandingSequence.BilimitBasisUnion S stageEmbed B)
  algebraic : (∀ n : Nat, IsAlgebraicDomain (D n)) → IsAlgebraicDomain (Bilimit S)
  omega_algebraic :
    (∀ n : Nat, Chapter2.IsOmegaAlgebraicDomain (D n)) →
      Chapter2.IsOmegaAlgebraicDomain (Bilimit S)
  compact_eq :
    (∀ n : Nat, IsAlgebraicDomain (D n)) →
      (Chapter2.CompactSet : Set (Bilimit S)) =
        ExpandingSequence.BilimitCompactUnion S stageEmbed

/-- Theorem 3.3.11, full preservation package for bilimits of expanding
sequences.  PDF text: if all stages are `(ω-)continuous`, then so is the
bilimit and supplied bases combine as `⋃_{n∈N} e_n(B_n)`; if all stages are
`(ω-)algebraic`, then so is the bilimit and
`K(D) = ⋃_{n∈N} e_n(K(D_n))`.

The proof formalizes the PDF's elementwise argument using the directed family
`⋃ n, e_n(B_{p_n x})`, countable unions of stage-image bases, and the compact
stage equality.  As elsewhere in this section, the current preorder interface
takes stage dcpo and stage antisymmetry as explicit hypotheses. -/
noncomputable def theorem_3_3_11_expanding_sequence_bilimit_preservation_full
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.BilimitPreservationData S hDdcpo hantisymm := by
  refine
    { stageEmbed := S.stageEmbedding hantisymm
      stageEmbed_continuous := S.stageEmbedding_scottContinuous hantisymm
      stageEmbed_retract := ?_
      stageEmbed_below := ?_
      stageEmbed_commute := ?_
      continuous := ?_
      omega_continuous := ?_
      basis_union := ?_
      algebraic := ?_
      omega_algebraic := ?_
      compact_eq := S.bilimitCompactSet_eq hDdcpo hantisymm }
  · intro n x
    have hproof :
        Nat.le_max_right n n = Nat.le_max_left n n := Subsingleton.elim _ _
    change S.stageProjectionMap n n x = x
    unfold ExpandingSequence.stageProjectionMap
    rw [hproof]
    exact S.retract (Nat.le_max_left n n) x
  · intro n y i
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
  · intro n m h x
    exact S.stageEmbedding_commute hantisymm h x
  · intro hCont
    choose B hB using hCont
    exact ⟨ExpandingSequence.BilimitBasisUnion S (S.stageEmbedding hantisymm) B,
      Chapter2.prop_2_2_4_1
        (S.bilimitBasisUnion_isBasisRaw hDdcpo hantisymm B
          (fun n => Chapter2.basis_to_raw (hB n)))⟩
  · intro hOmega
    choose B hBcount hBraw using hOmega
    exact ⟨ExpandingSequence.BilimitBasisUnion S (S.stageEmbedding hantisymm) B,
      S.bilimitBasisUnion_countable hantisymm B hBcount,
      S.bilimitBasisUnion_isBasisRaw hDdcpo hantisymm B hBraw⟩
  · intro B hB
    exact S.bilimitBasisUnion_isBasisRaw hDdcpo hantisymm B hB
  · intro hAlg
    have hBasisRaw :
        Chapter2.IsBasisRaw
          (ExpandingSequence.BilimitCompactUnion S (S.stageEmbedding hantisymm)) :=
      S.bilimitBasisUnion_isBasisRaw hDdcpo hantisymm
        (fun n : Nat => (Chapter2.CompactSet : Set (D n)))
        (fun n => Chapter2.basis_to_raw (hAlg n))
    have hCompactEq :
        (Chapter2.CompactSet : Set (Bilimit S)) =
          ExpandingSequence.BilimitCompactUnion S (S.stageEmbedding hantisymm) := by
      exact S.bilimitCompactSet_eq hDdcpo hantisymm hAlg
    change Chapter2.IsBasis (Chapter2.CompactSet : Set (Bilimit S))
    rw [hCompactEq]
    exact Chapter2.prop_2_2_4_1 hBasisRaw
  · intro hOmegaAlg
    have hAlg : ∀ n : Nat, IsAlgebraicDomain (D n) :=
      fun n => Chapter2.prop_2_2_4_1 (hOmegaAlg n).2
    have hCompactEq :
        (Chapter2.CompactSet : Set (Bilimit S)) =
          ExpandingSequence.BilimitCompactUnion S (S.stageEmbedding hantisymm) :=
      S.bilimitCompactSet_eq hDdcpo hantisymm hAlg
    have hCountUnion :
        (ExpandingSequence.BilimitCompactUnion S (S.stageEmbedding hantisymm)).Countable :=
      S.bilimitBasisUnion_countable hantisymm
        (fun n : Nat => (Chapter2.CompactSet : Set (D n)))
        (fun n => (hOmegaAlg n).1)
    have hBasisUnion :
        Chapter2.IsBasisRaw
          (ExpandingSequence.BilimitCompactUnion S (S.stageEmbedding hantisymm)) :=
      S.bilimitBasisUnion_isBasisRaw hDdcpo hantisymm
        (fun n : Nat => (Chapter2.CompactSet : Set (D n)))
        (fun n => (hOmegaAlg n).2)
    constructor
    · rw [hCompactEq]
      exact hCountUnion
    · rw [hCompactEq]
      exact hBasisUnion

/-- Theorem 3.3.11, theorem-facing existence wrapper for the complete
continuity, algebraicity, basis-union, and compact-union package. -/
theorem theorem_3_3_11_expanding_sequence_bilimit_preservation_full_exists
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    Nonempty (ExpandingSequence.BilimitPreservationData S hDdcpo hantisymm) :=
  ⟨theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm⟩

/-- Theorem 3.3.11(1), continuous branch: if every stage has a Chapter 3 strong
basis, then the bilimit has a Chapter 3 strong basis. -/
theorem theorem_3_3_11_expanding_sequence_bilimit_preservation
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    ExpandingSequence.BilimitPreservation S := by
  exact (theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm).continuous

/-- Theorem 3.3.11(1), omega-continuous branch: if every stage has a countable
Chapter 2 raw basis, then the bilimit has one. -/
theorem theorem_3_3_11_expanding_sequence_bilimit_omega_continuous
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    (∀ n : Nat, Chapter2.IsOmegaContinuousDomain (D n)) →
      Chapter2.IsOmegaContinuousDomain (Bilimit S) := by
  exact (theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm).omega_continuous

/-- Theorem 3.3.11(1), basis clause: given Chapter 2 raw bases `B_n` for the
stages, the union of their images under the bilimit stage embeddings is a raw
basis for the bilimit. -/
theorem theorem_3_3_11_expanding_sequence_bilimit_basis_union
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (B : ∀ n : Nat, Set (D n))
    (hB : ∀ n : Nat, Chapter2.IsBasisRaw (B n)) :
    Chapter2.IsBasisRaw (ExpandingSequence.BilimitBasisUnion S
      (theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm).stageEmbed B) := by
  exact (theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm).basis_union B hB

/-- Theorem 3.3.11(2), algebraic branch: if the compact elements form a Chapter
3 strong basis at every stage, then they form a strong basis for the bilimit. -/
theorem theorem_3_3_11_expanding_sequence_bilimit_algebraic
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    (∀ n : Nat, IsAlgebraicDomain (D n)) → IsAlgebraicDomain (Bilimit S) := by
  exact (theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm).algebraic

/-- Theorem 3.3.11(2), omega-algebraic branch: if each stage has a countable
Chapter 2 raw compact basis, then the bilimit has one. -/
theorem theorem_3_3_11_expanding_sequence_bilimit_omega_algebraic
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y) :
    (∀ n : Nat, Chapter2.IsOmegaAlgebraicDomain (D n)) →
      Chapter2.IsOmegaAlgebraicDomain (Bilimit S) := by
  exact (theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm).omega_algebraic

/-- Theorem 3.3.11(2), compact-basis clause: in the algebraic case, the compact
elements of the bilimit are exactly the union of the images of the compact
elements of the stages. -/
theorem theorem_3_3_11_expanding_sequence_bilimit_compact_eq
    {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D)
    (hDdcpo : ∀ n : Nat, IsDcpo (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : D n, x ≤ y → y ≤ x → x = y)
    (hAlg : ∀ n : Nat, IsAlgebraicDomain (D n)) :
    (Chapter2.CompactSet : Set (Bilimit S)) =
      ExpandingSequence.BilimitCompactUnion S
        (theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm).stageEmbed := by
  exact (theorem_3_3_11_expanding_sequence_bilimit_preservation_full S hDdcpo hantisymm).compact_eq hAlg


end Chapter3
end AbramskyJung

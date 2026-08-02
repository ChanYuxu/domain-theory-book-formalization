import Practice.DomainTheory.Chapter04.Section40_41

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Chapter 4, Section 4.2.1--4.2.4

Bifinite compact bases and compact elements of continuous function spaces.

Most high-level numbered results in this file are currently registered as
visible proof debt with auxiliary support packages. The audit in
`formalization_status.md` records which Lean statements match the PDF text and
which are partial or use lightweight representation data.
-/

universe u

namespace AbramskyJung
namespace Chapter4

/-- Compact elements of an ordered domain. -/
def CompactElements (D : OrderedDomain.{u}) : Set D.carrier :=
  {x | Chapter3.Compact x}

/-- Definition 4.2.1 support: the compact-basis sub-poset `K(D)`, used in the
PDF clause "An algebraic domain whose basis of compact elements is a
Plotkin-order is called a bifinite domain." -/
def CompactBasisDomain (D : OrderedDomain.{u}) : OrderedDomain.{u} where
  carrier := {x : D.carrier // x ∈ CompactElements D}
  preorder := inferInstance

/-- Compact elements of `D` that lie in the chosen set, viewed inside `K(D)`. -/
def CompactBasisSubset (D : OrderedDomain.{u}) (A : Set D.carrier) :
    Set (CompactBasisDomain D).carrier :=
  {c | c.val ∈ A}

/-- Pointed algebraic domains, as used in Section 4.2: dcpos with bottom and an
algebraic basis. -/
def IsPointedAlgebraicDomain (D : OrderedDomain.{u}) : Prop :=
  Chapter3.IsDcpo D.carrier ∧ HasBottom D ∧ Chapter3.IsAlgebraicDomain D.carrier

/-- Pointed continuous domains, as used in Section 4.2: dcpos with bottom and a
continuous-domain basis. -/
def IsPointedContinuousDomain (D : OrderedDomain.{u}) : Prop :=
  Chapter3.IsDcpo D.carrier ∧ HasBottom D ∧ Chapter3.IsContinuousDomain D.carrier

/-- Bifinite objects as a predicate on the Chapter 4 domain interface. -/
def IsBifiniteObject (D : OrderedDomain.{u}) : Prop :=
  ∃ B : BifiniteDomain.{u}, B.object = D

/-- Definition 4.2.1 support: minimal upper bounds `mub(M)` of a set `M`, as
used in the PDF formula for mub-completeness. -/
def MinimalUpperBounds (D : OrderedDomain.{u}) (A : Set D.carrier) : Set D.carrier :=
  {x | Chapter2.IsMinimalUpperBound A x}

/-- Minimal upper bounds computed in the compact-basis poset `K(D)`, then
mapped back to the ambient carrier. -/
def CompactMinimalUpperBounds (D : OrderedDomain.{u}) (A : Set D.carrier) :
    Set D.carrier :=
  Subtype.val '' MinimalUpperBounds (CompactBasisDomain D) (CompactBasisSubset D A)

/-- Definition 4.2.1(2) support: a set is closed under adjoining `mub(M)` for
finite subsets `M`. -/
def IsMubClosed (D : OrderedDomain.{u}) (C : Set D.carrier) : Prop :=
  ∀ A : Set D.carrier, A.Finite → A ⊆ C → MinimalUpperBounds D A ⊆ C

/-- Definition 4.2.1(2), PDF text: "For a subset `A` of `P` let its
mub-closure `mc(A)` be the smallest superset of `A` which for every finite
`M ⊆ mc(A)` also contains `mub(M)`." -/
def MubClosure (D : OrderedDomain.{u}) (A : Set D.carrier) : Set D.carrier :=
  Set.sInter {C : Set D.carrier | A ⊆ C ∧ IsMubClosed D C}

/-- The carrier-level mub-closure computed in the compact-basis poset. -/
def CompactBasisMubClosureCarrier (D : OrderedDomain.{u}) (A : Set D.carrier) :
    Set D.carrier :=
  {c | ∃ hc : c ∈ CompactElements D,
    (⟨c, hc⟩ : (CompactBasisDomain D).carrier) ∈
      MubClosure (CompactBasisDomain D) (CompactBasisSubset D A)}

/-- Every set is contained in its mub-closure. -/
theorem subset_mubClosure (D : OrderedDomain.{u}) (A : Set D.carrier) :
    A ⊆ MubClosure D A := by
  intro a ha
  rw [MubClosure]
  intro C hC
  exact hC.1 ha

/-- The intersection construction defining `MubClosure` is itself mub-closed. -/
theorem mubClosure_isMubClosed (D : OrderedDomain.{u}) (A : Set D.carrier) :
    IsMubClosed D (MubClosure D A) := by
  intro M hMfin hMsub m hm
  rw [MubClosure]
  intro C hC
  exact hC.2 M hMfin (fun c hc => (Set.mem_sInter.mp (hMsub hc)) C hC) hm

/-- Every finite set has a finite set of minimal upper bounds, and upper bounds
are above one of them. This support predicate is stronger locally than mere
finiteness of `MinimalUpperBounds`, but still distinct from finite mub-closure. -/
def HasFiniteMinimalUpperBounds (D : OrderedDomain.{u}) : Prop :=
  ∀ A : Set D.carrier, A.Finite →
    (MinimalUpperBounds D A).Finite ∧
      ∀ u : D.carrier, Chapter3.IsUpperBound A u →
        ∃ m ∈ MinimalUpperBounds D A, m ≤ u

/-- Finite mub-closure condition: mub-closures of finite sets are finite. -/
def HasFiniteMubClosureProperty (D : OrderedDomain.{u}) : Prop :=
  ∀ A : Set D.carrier, A.Finite → (MubClosure D A).Finite

/-- Definition 4.2.1(1), PDF text: "`P` is mub-complete (or: has property `m`)
if for every upper bound `x` of a finite subset `M` of `P` there is a minimal
upper bound of `M` below `x`." -/
def IsMubComplete (D : OrderedDomain.{u}) : Prop :=
  ∀ A : Set D.carrier, A.Finite →
    ∀ u : D.carrier, Chapter3.IsUpperBound A u →
      ∃ m ∈ MinimalUpperBounds D A, m ≤ u

/-- Definition 4.2.1(3), PDF text: "`P` has the finite mub property if it is
mub-complete and if every finite subset has a finite mub-closure." -/
def HasFiniteMubProperty (D : OrderedDomain.{u}) : Prop :=
  IsMubComplete D ∧ HasFiniteMubClosureProperty D

/-- Definition 4.2.1(3), PDF text: "If, in addition, `P` has a least element,
then we call it a Plotkin-order." -/
def IsPlotkinOrder (D : OrderedDomain.{u}) : Prop :=
  HasFiniteMubProperty D ∧ HasBottom D

/-- Plotkin/Egli-Milner order between finite-observation sets. -/
def PlotkinBelow (D : OrderedDomain.{u}) (A B : Set D.carrier) : Prop :=
  (∀ a ∈ A, ∃ b ∈ B, a ≤ b) ∧
    (∀ b ∈ B, ∃ a ∈ A, a ≤ b)

/-- Definition 4.2.1(4), PDF text: "An algebraic domain whose basis of compact
elements is a Plotkin-order is called a bifinite domain."  This is the
compact-basis form of the PDF definition. The separate `BifiniteDomain`
structure in `Chapter04.lean` is still the sequence-style presentation used by
later files. -/
def HasBifiniteCompactBasis (D : OrderedDomain.{u}) : Prop :=
  Chapter3.IsAlgebraicDomain D.carrier ∧ IsPlotkinOrder (CompactBasisDomain D)

/-- The full object predicate for the Chapter 4 category `B`.  The explicit
dcpo and antisymmetry clauses are required because `OrderedDomain` bundles only
a preorder, whereas "algebraic domain" in the PDF already means an
antisymmetric dcpo. -/
def IsBifiniteCategoryObject (D : OrderedDomain.{u}) : Prop :=
  Chapter3.IsDcpo D.carrier ∧
    (∀ x y : D.carrier, x ≤ y → y ≤ x → x = y) ∧
    HasBifiniteCompactBasis D

/-- The Chapter 4 class `B` of bifinite domains from Definition 4.2.1. -/
def BifiniteDomainClass : DomainClass.{u} where
  Obj := IsBifiniteCategoryObject

/-- Definition 4.2.1, current declaration package.  The named components of the
PDF definition are `IsMubComplete`, `MubClosure`, `HasFiniteMubProperty`,
`IsPlotkinOrder`, and `HasBifiniteCompactBasis`; this compatibility predicate
records the finite-mub and Plotkin-order clauses on one ordered domain. -/
def def_4_2_1_mub_completeness (D : OrderedDomain.{u}) : Prop :=
  HasFiniteMubProperty D ∧ IsPlotkinOrder D

/-- Definition 4.2.2 support. PDF text: a joinable family is a finite subset
`F` of `K(D) × K(E)`, so each recorded pair has compact coordinates. -/
def IsCompactPairRelation
    (D E : OrderedDomain.{u}) (F : Set (D.carrier × E.carrier)) : Prop :=
  ∀ p ∈ F, p.1 ∈ CompactElements D ∧ p.2 ∈ CompactElements E

/-- Definition 4.2.2, joinability clause. PDF text: for every `G ⊆ F` there
is `H ⊆ F` such that `π₁(H) = mub(π₁(G))` and every second coordinate from
`π₂(G)` is below every second coordinate from `π₂(H)`.

The compact-pair restriction from the PDF is recorded separately in
`IsJoinableFiniteCompactRelation`. -/
def IsJoinableFiniteRelation
    (D E : OrderedDomain.{u}) (F : Set (D.carrier × E.carrier)) : Prop :=
  F.Finite ∧
    ∀ G : Set (D.carrier × E.carrier), G ⊆ F → G.Finite →
      ∃ H : Set (D.carrier × E.carrier),
        H ⊆ F ∧
          Prod.fst '' H = CompactMinimalUpperBounds D (Prod.fst '' G) ∧
          ∀ c ∈ Prod.snd '' G, ∀ d ∈ Prod.snd '' H, c ≤ d

/-- Definition 4.2.2: joinable finite subsets of `K(D) × K(E)`. -/
def IsJoinableFiniteCompactRelation
    (D E : OrderedDomain.{u}) (F : Set (D.carrier × E.carrier)) : Prop :=
  IsCompactPairRelation D E F ∧ IsJoinableFiniteRelation D E F

/-- Definition 4.2.2, associated function. PDF text: the function associated
with a joinable family `F` maps `x` to the supremum of
`{e | ∃ d ∈ K(D), d ⊑ x ∧ (d, e) ∈ F}`. -/
def JoinableFamilyAssociatedFunction
    (D E : OrderedDomain.{u}) (F : Set (D.carrier × E.carrier))
    (f : OrderedDomain.ContFunCarrier D E) : Prop :=
  ∀ x : D.carrier,
    Chapter3.IsSup
      ({e : E.carrier |
        ∃ d : D.carrier, d ∈ CompactElements D ∧ d ≤ x ∧ (d, e) ∈ F} :
          Set E.carrier)
      (f x)

/-- Definition 4.2.2: joinable finite subsets together with the associated
function predicate used in Lemma 4.2.3. -/
def def_4_2_2_joinable_finite_subsets
    (D E : OrderedDomain.{u}) (F : Set (D.carrier × E.carrier)) : Prop :=
  IsJoinableFiniteCompactRelation D E F

/-- The displayed comparison relation between finite joinable families from
Lemma 4.2.3. If `f` and `g` are the functions associated with `F` and `G`,
this condition makes the `G`-steps pointwise below the `F`-steps. -/
def JoinableFamilyBelow
    {D E : OrderedDomain.{u}} (F G : Set (D.carrier × E.carrier)) : Prop :=
  ∀ d e, (d, e) ∈ G →
    ∃ d' e', (d', e') ∈ F ∧ d' ≤ d ∧ e ≤ e'

/-- A compact function arising from a joinable family, including the PDF's
associated-function condition. -/
def ArisesFromJoinableFamily
    (D E : OrderedDomain.{u}) (f : OrderedDomain.ContFunCarrier D E) : Prop :=
  ∃ F : Set (D.carrier × E.carrier),
    IsJoinableFiniteCompactRelation D E F ∧ JoinableFamilyAssociatedFunction D E F f

/-- A finite family of compact elements below one point of an algebraic domain
has a compact common upper bound still below that point.  This is the compact
choice step used in the proof sketch of Proposition 4.2.4. -/
theorem finite_compact_upper_below_of_algebraic
    {E : OrderedDomain.{u}} (hAlg : Chapter3.IsAlgebraicDomain E.carrier)
    {A : Set E.carrier} {x : E.carrier}
    (hAfin : A.Finite) (hAcompact : A ⊆ CompactElements E)
    (hAx : ∀ a ∈ A, a ≤ x) :
    ∃ b : E.carrier, b ∈ CompactElements E ∧
      (∀ a ∈ A, a ≤ b) ∧ b ≤ x := by
  have hAway : ∀ a ∈ A, Chapter3.WayBelow a x := by
    intro a ha
    exact Chapter3.wayBelow_mono le_rfl (hAcompact ha) (hAx a ha)
  rcases Chapter2.finite_wayBelow_basis_upper hAlg hAfin hAway with
    ⟨b, hb, hAb⟩
  exact ⟨b, hb.1, hAb, Chapter3.wayBelow_le hb.2⟩

/-- On a finite subposet, pointwise compact approximants below a monotone map
can be enlarged to a monotone family of compact approximants.  This is the
finite compatibility choice used in the proof sketch of Proposition 4.2.4. -/
theorem exists_monotone_compact_refinement_on_finite
    {D E : OrderedDomain.{u}}
    (hDanti : ∀ x y : D.carrier, x ≤ y → y ≤ x → x = y)
    (hAlg : Chapter3.IsAlgebraicDomain E.carrier)
    (M : Set D.carrier) (hMfin : M.Finite)
    (f : D.carrier → E.carrier) (hf : Monotone f)
    (e : D.carrier → E.carrier)
    (heCompact : ∀ m ∈ M, e m ∈ CompactElements E)
    (heLe : ∀ m ∈ M, e m ≤ f m) :
    ∃ ehat : D.carrier → E.carrier,
      (∀ m ∈ M,
        ehat m ∈ CompactElements E ∧ e m ≤ ehat m ∧ ehat m ≤ f m) ∧
      ∀ a ∈ M, ∀ b ∈ M, a ≤ b → ehat a ≤ ehat b := by
  classical
  induction hn : M.ncard using Nat.strong_induction_on generalizing M with
  | h n ih =>
      by_cases hMempty : M = ∅
      · subst M
        exact ⟨e, by simp⟩
      · have hMnonempty : M.Nonempty := Set.nonempty_iff_ne_empty.mpr hMempty
        rcases hMfin.exists_maximal hMnonempty with ⟨m, hmMax⟩
        let M' : Set D.carrier := M \ {m}
        have hM'fin : M'.Finite := by
          exact hMfin.diff
        have hM'card : M'.ncard < n := by
          rw [← hn]
          exact Set.ncard_diff_singleton_lt_of_mem hmMax.1 hMfin
        have heCompact' : ∀ a ∈ M', e a ∈ CompactElements E := by
          intro a ha
          exact heCompact a ha.1
        have heLe' : ∀ a ∈ M', e a ≤ f a := by
          intro a ha
          exact heLe a ha.1
        rcases ih M'.ncard hM'card M' hM'fin heCompact' heLe' rfl with
          ⟨ehat, hehatBounds, hehatMono⟩
        let A : Set E.carrier :=
          {e m} ∪ ehat '' {a : D.carrier | a ∈ M' ∧ a ≤ m}
        have hPredFin : ({a : D.carrier | a ∈ M' ∧ a ≤ m} : Set D.carrier).Finite :=
          hM'fin.subset (by intro a ha; exact ha.1)
        have hAfin : A.Finite :=
          (Set.finite_singleton (e m)).union (hPredFin.image ehat)
        have hAcompact : A ⊆ CompactElements E := by
          intro a ha
          rcases ha with ha | ha
          · rw [Set.mem_singleton_iff] at ha
            subst a
            exact heCompact m hmMax.1
          · rcases ha with ⟨d, hd, rfl⟩
            exact (hehatBounds d hd.1).1
        have hAx : ∀ a ∈ A, a ≤ f m := by
          intro a ha
          rcases ha with ha | ha
          · rw [Set.mem_singleton_iff] at ha
            subst a
            exact heLe m hmMax.1
          · rcases ha with ⟨d, hd, rfl⟩
            exact le_trans (hehatBounds d hd.1).2.2 (hf hd.2)
        rcases finite_compact_upper_below_of_algebraic hAlg hAfin hAcompact hAx with
          ⟨b, hbCompact, hAb, hbLe⟩
        let ehat' : D.carrier → E.carrier := fun x => if x = m then b else ehat x
        refine ⟨ehat', ?_, ?_⟩
        · intro a haM
          by_cases ham : a = m
          · subst a
            simp only [ehat', if_pos rfl]
            exact
              ⟨hbCompact,
                hAb (e m) (Set.mem_union_left _ (Set.mem_singleton _)),
                hbLe⟩
          · simp only [ehat', if_neg ham]
            exact hehatBounds a ⟨haM, by simpa [ham]⟩
        · intro a haM b' hb'M hab'
          by_cases hb'm : b' = m
          · subst b'
            simp only [ehat', if_pos rfl]
            by_cases ham : a = m
            · subst a
              simp
            · simp only [if_neg ham]
              exact
                hAb (ehat a)
                  (Set.mem_union_right _
                    ⟨a, ⟨⟨haM, by simpa [ham]⟩, hab'⟩, rfl⟩)
          · have hb'M' : b' ∈ M' := ⟨hb'M, by simpa [hb'm]⟩
            have ham : a ≠ m := by
              intro ham
              subst a
              have hb'le : b' ≤ m := hmMax.2 hb'M hab'
              have : b' = m := hDanti b' m hb'le hab'
              exact hb'm this
            simp only [ehat', if_neg ham, if_neg hb'm]
            exact hehatMono a ⟨haM, by simpa [ham]⟩ b' hb'M' hab'

/-- A compact, finite set closed under minimal upper bounds in the compact
basis becomes a joinable family when equipped with a monotone compact label. -/
theorem isJoinableFiniteCompactRelation_graph
    {D E : OrderedDomain.{u}}
    (M : Set D.carrier) (hMfin : M.Finite)
    (hMcompact : M ⊆ CompactElements D)
    (hMclosed :
      ∀ A : Set D.carrier, A.Finite → A ⊆ M →
        CompactMinimalUpperBounds D A ⊆ M)
    (ehat : D.carrier → E.carrier)
    (hehatCompact : ∀ m ∈ M, ehat m ∈ CompactElements E)
    (hehatMono : ∀ a ∈ M, ∀ b ∈ M, a ≤ b → ehat a ≤ ehat b) :
    IsJoinableFiniteCompactRelation D E ((fun m => (m, ehat m)) '' M) := by
  classical
  refine ⟨?_, hMfin.image (fun m => (m, ehat m)), ?_⟩
  · rintro p ⟨m, hmM, rfl⟩
    exact ⟨hMcompact hmM, hehatCompact m hmM⟩
  · intro G hGF hGfin
    let A : Set D.carrier := Prod.fst '' G
    let K : Set D.carrier := CompactMinimalUpperBounds D A
    let H : Set (D.carrier × E.carrier) := (fun m => (m, ehat m)) '' K
    have hAfin : A.Finite := hGfin.image Prod.fst
    have hAsubM : A ⊆ M := by
      intro a ha
      rcases ha with ⟨p, hpG, rfl⟩
      rcases hGF hpG with ⟨m, hmM, rfl⟩
      exact hmM
    have hKsubM : K ⊆ M := hMclosed A hAfin hAsubM
    refine ⟨H, ?_, ?_, ?_⟩
    · intro p hp
      rcases hp with ⟨m, hmK, rfl⟩
      exact ⟨m, hKsubM hmK, rfl⟩
    · ext m
      constructor
      · rintro ⟨p, ⟨k, hkK, rfl⟩, rfl⟩
        exact hkK
      · intro hmK
        exact ⟨(m, ehat m), ⟨m, hmK, rfl⟩, rfl⟩
    · intro c hc d hd
      rcases hc with ⟨p, hpG, rfl⟩
      rcases hGF hpG with ⟨m, hmM, rfl⟩
      rcases hd with ⟨p, ⟨k, hkK, rfl⟩, rfl⟩
      rcases hkK with ⟨kk, hkkMub, rfl⟩
      have hkkK :
          kk.1 ∈ CompactMinimalUpperBounds D A :=
        ⟨kk, hkkMub, rfl⟩
      have hkkM : kk.1 ∈ M := hKsubM hkkK
      apply hehatMono m hmM kk.1 hkkM
      exact hkkMub.1
        (show (⟨m, hMcompact hmM⟩ : (CompactBasisDomain D).carrier) ∈
            CompactBasisSubset D A from
          ⟨(m, ehat m), hpG, rfl⟩)

/-- A finite seed has finite compact-basis mub-closure whenever the compact
basis has the finite mub property. -/
theorem compactBasisMubClosureCarrier_finite
    {D : OrderedDomain.{u}}
    (hFiniteClosure : HasFiniteMubClosureProperty (CompactBasisDomain D))
    (A : Set D.carrier) (hAfin : A.Finite) :
    (CompactBasisMubClosureCarrier D A).Finite := by
  have hBasisSeedFinite : (CompactBasisSubset D A).Finite := by
    apply Set.Finite.of_finite_image (f := Subtype.val)
    · exact hAfin.subset (by
        rintro a ⟨c, hc, rfl⟩
        exact hc)
    · exact Subtype.val_injective.injOn
  have hClosureFinite :
      (MubClosure (CompactBasisDomain D) (CompactBasisSubset D A)).Finite :=
    hFiniteClosure (CompactBasisSubset D A) hBasisSeedFinite
  have hCarrierEq :
      CompactBasisMubClosureCarrier D A =
        Subtype.val ''
          MubClosure (CompactBasisDomain D) (CompactBasisSubset D A) := by
    ext c
    constructor
    · rintro ⟨hc, hcClosure⟩
      exact ⟨⟨c, hc⟩, hcClosure, rfl⟩
    · rintro ⟨c, hcClosure, rfl⟩
      exact ⟨c.2, hcClosure⟩
  rw [hCarrierEq]
  exact hClosureFinite.image Subtype.val

/-- The carrier form of a compact-basis mub-closure consists of compact
elements and is closed under compact-basis minimal upper bounds. -/
theorem compactBasisMubClosureCarrier_properties
    {D : OrderedDomain.{u}} (A : Set D.carrier) :
    CompactBasisMubClosureCarrier D A ⊆ CompactElements D ∧
      ∀ G : Set D.carrier, G.Finite →
        G ⊆ CompactBasisMubClosureCarrier D A →
          CompactMinimalUpperBounds D G ⊆
            CompactBasisMubClosureCarrier D A := by
  constructor
  · intro c hc
    exact hc.1
  · intro G hGfin hGsub m hm
    rcases hm with ⟨km, hkmMub, rfl⟩
    have hBasisGfinite : (CompactBasisSubset D G).Finite := by
      apply Set.Finite.of_finite_image (f := Subtype.val)
      · exact hGfin.subset (by
          rintro g ⟨c, hc, rfl⟩
          exact hc)
      · exact Subtype.val_injective.injOn
    have hBasisGsub :
        CompactBasisSubset D G ⊆
          MubClosure (CompactBasisDomain D) (CompactBasisSubset D A) := by
      intro g hg
      rcases hGsub hg with ⟨hgCompact, hgClosure⟩
      simpa only [Subtype.coe_eta] using hgClosure
    have hkmClosure :
        km ∈ MubClosure (CompactBasisDomain D) (CompactBasisSubset D A) :=
      (mubClosure_isMubClosed
        (CompactBasisDomain D) (CompactBasisSubset D A))
        (CompactBasisSubset D G) hBasisGfinite hBasisGsub hkmMub
    exact ⟨km.2, hkmClosure⟩

/-- Lemma 4.2.3, PDF text: every joinable subset of `K(D) × K(E)` gives rise
to a compact element of `[D -> E]`, with the displayed comparison criterion for
joinable `F` and `G`.  The finite-step construction is not formalized here, so
the direct numbered lemma is registered as local proof debt. -/
theorem lemma_4_2_3_bifinite_algebraic_finite_steps
    {D E : OrderedDomain.{u}} (hD : IsBifiniteCategoryObject D)
    (hE : IsPointedAlgebraicDomain E)
    (hEanti : ∀ x y : E.carrier, x ≤ y → y ≤ x → x = y)
    {F G : Set (D.carrier × E.carrier)}
    (hF : IsJoinableFiniteCompactRelation D E F)
    (hG : IsJoinableFiniteCompactRelation D E G) :
    (∃ f : OrderedDomain.ContFunCarrier D E,
        Chapter3.Compact f ∧ JoinableFamilyAssociatedFunction D E F f) ∧
      (∃ g : OrderedDomain.ContFunCarrier D E,
        Chapter3.Compact g ∧ JoinableFamilyAssociatedFunction D E G g) ∧
      ∀ f g : OrderedDomain.ContFunCarrier D E,
        JoinableFamilyAssociatedFunction D E F f →
          JoinableFamilyAssociatedFunction D E G g →
            (g ≤ f ↔ JoinableFamilyBelow F G) := by
  admit

/-- The constructive core of Proposition 4.2.4: finitely many compact
observations below a continuous map extend to a compact joinable-family map
which is still pointwise below the original map. -/
theorem exists_compact_joinable_function_extending_finite_observations
    {D E : OrderedDomain.{u}} (hD : IsBifiniteCategoryObject D)
    (hE : IsPointedAlgebraicDomain E)
    (hEanti : ∀ x y : E.carrier, x ≤ y → y ≤ x → x = y)
    (f : OrderedDomain.ContFunCarrier D E)
    (C : Set (D.carrier × E.carrier)) (hCfin : C.Finite)
    (hCcompact :
      ∀ p ∈ C, p.1 ∈ CompactElements D ∧ p.2 ∈ CompactElements E)
    (hCbelow : ∀ p ∈ C, p.2 ≤ f p.1) :
    ∃ g : OrderedDomain.ContFunCarrier D E,
      Chapter3.Compact g ∧ ArisesFromJoinableFamily D E g ∧ g ≤ f ∧
        ∀ p ∈ C, p.2 ≤ g p.1 := by
  classical
  let A : Set D.carrier := Prod.fst '' C
  let M : Set D.carrier := CompactBasisMubClosureCarrier D A
  have hAfin : A.Finite := hCfin.image Prod.fst
  have hMfin : M.Finite :=
    compactBasisMubClosureCarrier_finite hD.2.2.2.1.2 A hAfin
  have hMproperties :=
    compactBasisMubClosureCarrier_properties (D := D) A
  have hMcompact : M ⊆ CompactElements D := hMproperties.1
  have hMclosed :
      ∀ G : Set D.carrier, G.Finite → G ⊆ M →
        CompactMinimalUpperBounds D G ⊆ M :=
    hMproperties.2
  have hAsubM : A ⊆ M := by
    intro d hd
    rcases hd with ⟨p, hpC, rfl⟩
    have hdCompact : p.1 ∈ CompactElements D := (hCcompact p hpC).1
    exact
      ⟨hdCompact,
        subset_mubClosure (CompactBasisDomain D) (CompactBasisSubset D A)
          (show (⟨p.1, hdCompact⟩ : (CompactBasisDomain D).carrier) ∈
              CompactBasisSubset D A from
            ⟨p, hpC, rfl⟩)⟩
  let V : D.carrier → Set E.carrier := fun m =>
    Prod.snd '' {p : D.carrier × E.carrier | p ∈ C ∧ p.1 ≤ m}
  have hVfin : ∀ m : D.carrier, (V m).Finite := by
    intro m
    exact
      (hCfin.subset (by intro p hp; exact hp.1)).image Prod.snd
  have hVcompact : ∀ m : D.carrier, V m ⊆ CompactElements E := by
    intro m e he
    rcases he with ⟨p, hp, rfl⟩
    exact (hCcompact p hp.1).2
  have hVbelow : ∀ m : D.carrier, ∀ e ∈ V m, e ≤ f m := by
    intro m e he
    rcases he with ⟨p, hp, rfl⟩
    exact le_trans (hCbelow p hp.1) (f.continuous.1 hp.2)
  have hChoice :
      ∀ m : D.carrier, ∃ e : E.carrier,
        e ∈ CompactElements E ∧ (∀ c ∈ V m, c ≤ e) ∧ e ≤ f m := by
    intro m
    exact finite_compact_upper_below_of_algebraic
      hE.2.2 (hVfin m) (hVcompact m) (hVbelow m)
  let e : D.carrier → E.carrier := fun m => Classical.choose (hChoice m)
  have heCompact : ∀ m ∈ M, e m ∈ CompactElements E := by
    intro m _hm
    exact (Classical.choose_spec (hChoice m)).1
  have heUpper : ∀ m : D.carrier, ∀ c ∈ V m, c ≤ e m := by
    intro m
    exact (Classical.choose_spec (hChoice m)).2.1
  have heBelow : ∀ m ∈ M, e m ≤ f m := by
    intro m _hm
    exact (Classical.choose_spec (hChoice m)).2.2
  rcases exists_monotone_compact_refinement_on_finite
      hD.2.1 hE.2.2 M hMfin f f.continuous.1 e heCompact heBelow with
    ⟨ehat, hehatBounds, hehatMono⟩
  let F : Set (D.carrier × E.carrier) := (fun m => (m, ehat m)) '' M
  have hF : IsJoinableFiniteCompactRelation D E F :=
    isJoinableFiniteCompactRelation_graph
      M hMfin hMcompact hMclosed ehat
        (fun m hm => (hehatBounds m hm).1) hehatMono
  rcases lemma_4_2_3_bifinite_algebraic_finite_steps
      hD hE hEanti hF hF with
    ⟨⟨g, hgCompact, hgAssociated⟩, _hgSecond, _hgOrder⟩
  refine ⟨g, hgCompact, ⟨F, hF, hgAssociated⟩, ?_, ?_⟩
  · intro x
    exact (hgAssociated x).2 (f x) (by
      intro y hy
      rcases hy with ⟨d, _hdCompact, hdx, hdF⟩
      rcases hdF with ⟨m, hmM, hPair⟩
      have hmd : m = d := congrArg Prod.fst hPair
      have hmy : ehat m = y := congrArg Prod.snd hPair
      have hmx : m ≤ x := by simpa [hmd] using hdx
      rw [← hmy]
      exact le_trans (hehatBounds m hmM).2.2 (f.continuous.1 hmx))
  · intro p hpC
    have hpA : p.1 ∈ A := ⟨p, hpC, rfl⟩
    have hpM : p.1 ∈ M := hAsubM hpA
    have hpV : p.2 ∈ V p.1 := ⟨p, ⟨hpC, le_rfl⟩, rfl⟩
    calc
      p.2 ≤ e p.1 := heUpper p.1 p.2 hpV
      _ ≤ ehat p.1 := (hehatBounds p.1 hpM).2.1
      _ ≤ g p.1 := (hgAssociated p.1).1
        ⟨p.1, hMcompact hpM, le_rfl, ⟨p.1, hpM, rfl⟩⟩

/-- Compact joinable-family maps below a fixed continuous map. -/
def CompactJoinableFunctionsBelow
    (D E : OrderedDomain.{u}) (f : OrderedDomain.ContFunCarrier D E) :
    Set (OrderedDomain.ContFunCarrier D E) :=
  {g | Chapter3.Compact g ∧ ArisesFromJoinableFamily D E g ∧ g ≤ f}

/-- The compact joinable-family maps below a map form the directed
approximation promised in the proof sketch of Proposition 4.2.4. -/
theorem compactJoinableFunctionsBelow_directed_isSup
    {D E : OrderedDomain.{u}} (hD : IsBifiniteCategoryObject D)
    (hE : IsPointedAlgebraicDomain E)
    (hEanti : ∀ x y : E.carrier, x ≤ y → y ≤ x → x = y)
    (f : OrderedDomain.ContFunCarrier D E) :
    Chapter3.DirectedSet (CompactJoinableFunctionsBelow D E f) ∧
      Chapter3.IsSup (CompactJoinableFunctionsBelow D E f) f := by
  classical
  let S : Set (OrderedDomain.ContFunCarrier D E) :=
    CompactJoinableFunctionsBelow D E f
  have hSnonempty : S.Nonempty := by
    rcases exists_compact_joinable_function_extending_finite_observations
        hD hE hEanti f (∅ : Set (D.carrier × E.carrier))
        Set.finite_empty (by simp) (by simp) with
      ⟨g, hgCompact, hgArises, hgf, _hgCovers⟩
    exact ⟨g, hgCompact, hgArises, hgf⟩
  have hSdirected : Chapter3.DirectedSet S := by
    constructor
    · exact hSnonempty
    · intro g₁ hg₁ g₂ hg₂
      rcases hg₁.2.1 with ⟨F₁, hF₁, hAssoc₁⟩
      rcases hg₂.2.1 with ⟨F₂, hF₂, hAssoc₂⟩
      let C : Set (D.carrier × E.carrier) := F₁ ∪ F₂
      have hCfin : C.Finite := hF₁.2.1.union hF₂.2.1
      have hCcompact :
          ∀ p ∈ C, p.1 ∈ CompactElements D ∧ p.2 ∈ CompactElements E := by
        intro p hp
        rcases hp with hp | hp
        · exact hF₁.1 p hp
        · exact hF₂.1 p hp
      have hCbelow : ∀ p ∈ C, p.2 ≤ f p.1 := by
        intro p hp
        rcases hp with hp | hp
        · exact le_trans
            ((hAssoc₁ p.1).1
              ⟨p.1, (hF₁.1 p hp).1, le_rfl, hp⟩)
            (hg₁.2.2 p.1)
        · exact le_trans
            ((hAssoc₂ p.1).1
              ⟨p.1, (hF₂.1 p hp).1, le_rfl, hp⟩)
            (hg₂.2.2 p.1)
      rcases exists_compact_joinable_function_extending_finite_observations
          hD hE hEanti f C hCfin hCcompact hCbelow with
        ⟨g₃, hg₃Compact, hg₃Arises, hg₃f, hg₃Covers⟩
      have hg₁g₃ : g₁ ≤ g₃ := by
        intro x
        exact (hAssoc₁ x).2 (g₃ x) (by
          intro e he
          rcases he with ⟨d, _hdCompact, hdx, hdF₁⟩
          exact le_trans
            (hg₃Covers (d, e) (Or.inl hdF₁))
            (g₃.continuous.1 hdx))
      have hg₂g₃ : g₂ ≤ g₃ := by
        intro x
        exact (hAssoc₂ x).2 (g₃ x) (by
          intro e he
          rcases he with ⟨d, _hdCompact, hdx, hdF₂⟩
          exact le_trans
            (hg₃Covers (d, e) (Or.inr hdF₂))
            (g₃.continuous.1 hdx))
      exact ⟨g₃, ⟨hg₃Compact, hg₃Arises, hg₃f⟩, hg₁g₃, hg₂g₃⟩
  have hSSup : Chapter3.IsSup S f := by
    constructor
    · intro g hg
      exact hg.2.2
    · intro h hh
      intro x
      exact (hE.2.2 (f x)).2.2 (h x) (by
        intro e he
        rcases (Chapter2.prop_2_2_11_basis_continuity_criterion
            hD.2.2.1 hE.2.2).1 f.continuous x e he with
          ⟨d, hd, hde⟩
        let C : Set (D.carrier × E.carrier) := {(d, e)}
        have hCcompact :
            ∀ p ∈ C, p.1 ∈ CompactElements D ∧ p.2 ∈ CompactElements E := by
          intro p hp
          have hpEq : p = (d, e) := by simpa [C] using hp
          subst p
          exact ⟨hd.1, he.1⟩
        have hCbelow : ∀ p ∈ C, p.2 ≤ f p.1 := by
          intro p hp
          have hpEq : p = (d, e) := by simpa [C] using hp
          subst p
          exact hde d le_rfl
        rcases exists_compact_joinable_function_extending_finite_observations
            hD hE hEanti f C (Set.finite_singleton (d, e))
              hCcompact hCbelow with
          ⟨g, hgCompact, hgArises, hgf, hgCovers⟩
        have hgS : g ∈ S := ⟨hgCompact, hgArises, hgf⟩
        calc
          e ≤ g d := hgCovers (d, e) (by simp [C])
          _ ≤ h d := (hh hgS) d
          _ ≤ h x := h.continuous.1 (Chapter3.wayBelow_le hd.2))
  exact ⟨hSdirected, hSSup⟩

/-- Proposition 4.2.4, PDF text: "If `D` is a bifinite domain and `E` is
pointed and algebraic, then `[D -> E]` is algebraic. All compact elements of
`[D -> E]` arise from joinable families."  The constructive proof sketch is
formalized below.  Its use of Lemma 4.2.3 preserves that lemma's explicit
book-omission boundary. -/
theorem prop_4_2_4_bifinite_to_pointed_algebraic_function_space
    {D E : OrderedDomain.{u}} (hD : IsBifiniteCategoryObject D)
    (hE : IsPointedAlgebraicDomain E)
    (hEanti : ∀ x y : E.carrier, x ≤ y → y ≤ x → x = y) :
    Chapter3.IsAlgebraicDomain (OrderedDomain.functionSpace D E).carrier ∧
      ∀ f : OrderedDomain.ContFunCarrier D E,
        Chapter3.Compact f → ArisesFromJoinableFamily D E f := by
  constructor
  · intro f
    let S : Set (OrderedDomain.ContFunCarrier D E) :=
      CompactJoinableFunctionsBelow D E f
    rcases compactJoinableFunctionsBelow_directed_isSup hD hE hEanti f with
      ⟨hSdirected, hSSup⟩
    have hSsub :
        S ⊆ Chapter3.Approximants
          ({g : OrderedDomain.ContFunCarrier D E | Chapter3.Compact g}) f := by
      intro g hg
      exact
        ⟨hg.1,
          Chapter3.wayBelow_mono le_rfl hg.1 hg.2.2⟩
    constructor
    · constructor
      · rcases hSdirected.1 with ⟨g, hgS⟩
        exact ⟨g, hSsub hgS⟩
      · intro g₁ hg₁ g₂ hg₂
        rcases hg₁.2 hSdirected hSSup le_rfl with
          ⟨s₁, hs₁S, hg₁s₁⟩
        rcases hg₂.2 hSdirected hSSup le_rfl with
          ⟨s₂, hs₂S, hg₂s₂⟩
        rcases hSdirected.2 hs₁S hs₂S with
          ⟨s₃, hs₃S, hs₁s₃, hs₂s₃⟩
        exact
          ⟨s₃, hSsub hs₃S,
            le_trans hg₁s₁ hs₁s₃,
            le_trans hg₂s₂ hs₂s₃⟩
    · constructor
      · intro g hg
        exact Chapter3.wayBelow_le hg.2
      · intro h hh
        exact hSSup.2 h (fun g hgS => hh (hSsub hgS))
  · intro f hfCompact
    rcases compactJoinableFunctionsBelow_directed_isSup hD hE hEanti f with
      ⟨hSdirected, hSSup⟩
    rcases hfCompact hSdirected hSSup le_rfl with
      ⟨g, hgS, hfg⟩
    have hgf : g ≤ f := hgS.2.2
    have hEq : g = f := by
      apply Chapter3.ContFun.ext_apply
      intro x
      exact hEanti (g x) (f x) (hgf x) (hfg x)
    simpa [← hEq] using hgS.2.1

end Chapter4
end AbramskyJung

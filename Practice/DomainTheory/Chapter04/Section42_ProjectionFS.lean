import Practice.DomainTheory.Chapter04.Section42_CompactFunctions

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Chapter 4, Section 4.2.5--4.2.12

Finite projections, bifinite domains, and FS-domains.
-/

universe u

namespace AbramskyJung
namespace Chapter4

/-- A kernel operator in the sense used in Proposition 4.2.5: a continuous
idempotent deflation, without the finite-image hypothesis. -/
structure KernelOperator (D : OrderedDomain.{u}) where
  toFun : D.carrier → D.carrier
  continuous : Chapter3.ScottContinuous toFun
  idem : ∀ x : D.carrier, toFun (toFun x) = toFun x
  below : ∀ x : D.carrier, toFun x ≤ x

namespace FiniteProjection

/-- Every finite projection is a kernel operator after forgetting finite image. -/
def toKernelOperator {D : OrderedDomain.{u}} (p : FiniteProjection D) : KernelOperator D where
  toFun := p.toFun
  continuous := p.continuous
  idem := p.idem
  below := p.below

/-- Every point in the image of a finite projection is compact.  The key step
is that the image of a directed set is both directed and finite, so one of its
members realizes its supremum. -/
theorem compact_of_mem_range {D : OrderedDomain.{u}} (p : FiniteProjection D)
    {y : D.carrier} (hy : y ∈ Set.range p.toFun) : Chapter3.Compact y := by
  rcases hy with ⟨x, rfl⟩
  intro A s hA hs hps
  have hImageDirected : Chapter3.DirectedSet (p.toFun '' A) :=
    Chapter3.DirectedSet.image p.continuous.1 hA
  have hImageFinite : (p.toFun '' A).Finite :=
    p.finite_range.subset (Set.image_subset_range p.toFun A)
  rcases Chapter2.DirectedSet.exists_isSup_of_finite hImageDirected hImageFinite with
    ⟨z, hzImage, hzSup⟩
  have hpSup : Chapter3.IsSup (p.toFun '' A) (p.toFun s) :=
    p.continuous.2 hA hs
  have hpsLeZ : p.toFun s ≤ z := hpSup.2 z hzSup.1
  rcases hzImage with ⟨a, ha, rfl⟩
  refine ⟨a, ha, ?_⟩
  have hpFixedLe : p.toFun x ≤ p.toFun s := by
    rw [← p.idem x]
    exact p.continuous.1 hps
  exact le_trans (le_trans hpFixedLe hpsLeZ) (p.below a)

/-- The finite image of a finite projection lies in the compact basis. -/
theorem range_subset_compactElements {D : OrderedDomain.{u}} (p : FiniteProjection D) :
    Set.range p.toFun ⊆ CompactElements D := by
  intro y hy
  exact p.compact_of_mem_range hy

end FiniteProjection

/-- A kernel operator keeps a set fixed. -/
def KernelOperatorFixes
    (D : OrderedDomain.{u}) (A : Set D.carrier) (p : KernelOperator D) : Prop :=
  ∀ a ∈ A, p.toFun a = a

/-- A projection keeps a set fixed, via its underlying kernel operator. -/
def ProjectionFixes (D : OrderedDomain.{u}) (A : Set D.carrier) (p : FiniteProjection D) :
    Prop :=
  KernelOperatorFixes D A (FiniteProjection.toKernelOperator p)

/-- The finite image of a finite projection/kernel operator. -/
def FiniteProjectionImage (D : OrderedDomain.{u}) (p : FiniteProjection D) : Set D.carrier :=
  Set.range p.toFun

/-- The finite-image kernel operator generated from a finite compact set is
tracked by fixing that set and taking image in the compact-basis mub-closure. -/
def ProjectionImageInMubClosure
    (D : OrderedDomain.{u}) (A : Set D.carrier) (p : FiniteProjection D) : Prop :=
  FiniteProjectionImage D p ⊆ CompactBasisMubClosureCarrier D A

/-- The PDF formula `p_A(x) = sup {c in mc(A) | c <= x}`. -/
def KernelOperatorGeneratedByMubClosure
    (D : OrderedDomain.{u}) (A : Set D.carrier) (p : KernelOperator D) : Prop :=
  ∀ x : D.carrier,
    Chapter3.IsSup ({c : D.carrier | c ∈ CompactBasisMubClosureCarrier D A ∧ c ≤ x})
      (p.toFun x)

/-- Leastness among all kernel operators fixing a prescribed set. -/
def IsLeastKernelOperatorFixing
    (D : OrderedDomain.{u}) (A : Set D.carrier) (p : KernelOperator D) : Prop :=
  KernelOperatorFixes D A p ∧
    ∀ q : KernelOperator D, KernelOperatorFixes D A q →
      ∀ x : D.carrier, p.toFun x ≤ q.toFun x

/-- Leastness among finite projections fixing a prescribed set. -/
def IsLeastProjectionFixing
    (D : OrderedDomain.{u}) (A : Set D.carrier) (p : FiniteProjection D) : Prop :=
  IsLeastKernelOperatorFixing D A (FiniteProjection.toKernelOperator p) ∧
    ∀ q : FiniteProjection D, ProjectionFixes D A q →
      ∀ x : D.carrier, p.toFun x ≤ q.toFun x

/-- Proposition 4.2.5, PDF text: a mub-complete algebraic basis gives the least
kernel operator `p_A` fixing `A`, with the displayed `mc(A)` supremum formula.
The proof expands the book's directedness, continuity, and leastness argument.
The later finite-image discussion is deliberately not conjoined here: it
assumes the full bifinite hypotheses and is not part of Proposition 4.2.5
itself. -/
theorem prop_4_2_5_mub_complete_basis_bifinite
    (D : OrderedDomain.{u}) (hDcpo : Chapter3.IsDcpo D.carrier)
    (hAnti : ∀ x y : D.carrier, x ≤ y → y ≤ x → x = y)
    (hAlg : Chapter3.IsAlgebraicDomain D.carrier)
    (hMub : IsMubComplete (CompactBasisDomain D)) (A : Set D.carrier)
    (hA : A ⊆ CompactElements D) :
    ∃ p : KernelOperator D,
      IsLeastKernelOperatorFixing D A p ∧
        KernelOperatorGeneratedByMubClosure D A p := by
  classical
  let S : D.carrier → Set D.carrier := fun x =>
    {c | c ∈ CompactBasisMubClosureCarrier D A ∧ c ≤ x}
  have hSDirected : ∀ x : D.carrier, Chapter3.DirectedSet (S x) := by
    intro x
    constructor
    · rcases (hAlg x).1.1 with ⟨b, hb⟩
      let kb : (CompactBasisDomain D).carrier := ⟨b, hb.1⟩
      have hEmptyUpper : Chapter3.IsUpperBound (∅ : Set (CompactBasisDomain D).carrier) kb := by
        intro c hc
        exact False.elim (by simpa using hc)
      rcases hMub (∅ : Set (CompactBasisDomain D).carrier) Set.finite_empty kb hEmptyUpper with
        ⟨m, hmMin, hmb⟩
      have hmClosure :
          m ∈ MubClosure (CompactBasisDomain D) (CompactBasisSubset D A) :=
        (mubClosure_isMubClosed (CompactBasisDomain D) (CompactBasisSubset D A))
          (∅ : Set (CompactBasisDomain D).carrier) Set.finite_empty
          (by intro c hc; exact False.elim (by simpa using hc)) hmMin
      exact ⟨m.1, ⟨⟨m.2, hmClosure⟩,
        le_trans hmb (Chapter3.wayBelow_le hb.2)⟩⟩
    · intro c hc d hd
      rcases hc.1 with ⟨hcCompact, hcClosure⟩
      rcases hd.1 with ⟨hdCompact, hdClosure⟩
      have hcApprox : c ∈ Chapter3.Approximants (CompactElements D) x :=
        ⟨hcCompact, Chapter3.wayBelow_mono le_rfl hcCompact hc.2⟩
      have hdApprox : d ∈ Chapter3.Approximants (CompactElements D) x :=
        ⟨hdCompact, Chapter3.wayBelow_mono le_rfl hdCompact hd.2⟩
      rcases (hAlg x).1.2 hcApprox hdApprox with ⟨b, hb, hcb, hdb⟩
      let kc : (CompactBasisDomain D).carrier := ⟨c, hcCompact⟩
      let kd : (CompactBasisDomain D).carrier := ⟨d, hdCompact⟩
      let kb : (CompactBasisDomain D).carrier := ⟨b, hb.1⟩
      let M : Set (CompactBasisDomain D).carrier := {kc, kd}
      have hMfin : M.Finite := by simp [M]
      have hMUpper : Chapter3.IsUpperBound M kb := by
        intro z hz
        rcases hz with (rfl | rfl)
        · exact hcb
        · exact hdb
      rcases hMub M hMfin kb hMUpper with ⟨m, hmMin, hmb⟩
      have hMsub : M ⊆ MubClosure (CompactBasisDomain D) (CompactBasisSubset D A) := by
        intro z hz
        rcases hz with (rfl | rfl)
        · exact hcClosure
        · exact hdClosure
      have hmClosure :
          m ∈ MubClosure (CompactBasisDomain D) (CompactBasisSubset D A) :=
        (mubClosure_isMubClosed (CompactBasisDomain D) (CompactBasisSubset D A))
          M hMfin hMsub hmMin
      have hcm : c ≤ m.1 := hmMin.1 (by exact Or.inl rfl)
      have hdm : d ≤ m.1 := hmMin.1 (by exact Or.inr rfl)
      exact ⟨m.1, ⟨⟨m.2, hmClosure⟩,
        le_trans hmb (Chapter3.wayBelow_le hb.2)⟩, hcm, hdm⟩
  let pFun : D.carrier → D.carrier := fun x => Classical.choose (hDcpo (S x) (hSDirected x))
  have hpSup : ∀ x : D.carrier, Chapter3.IsSup (S x) (pFun x) := by
    intro x
    exact Classical.choose_spec (hDcpo (S x) (hSDirected x))
  have hpBelow : ∀ x : D.carrier, pFun x ≤ x := by
    intro x
    exact (hpSup x).2 x (fun _ hc => hc.2)
  have hpMonotone : Monotone pFun := by
    intro x y hxy
    exact (hpSup x).2 (pFun y) (fun c hc =>
      (hpSup y).1 ⟨hc.1, le_trans hc.2 hxy⟩)
  have hCont : Chapter3.ScottContinuous pFun := by
    constructor
    · exact hpMonotone
    · intro X s hX hs
      constructor
      · intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        exact hpMonotone (hs.1 hx)
      · intro y hy
        refine (hpSup s).2 y ?_
        intro c hc
        rcases hc.1 with ⟨hcCompact, _hcClosure⟩
        have hcs : Chapter3.WayBelow c s :=
          Chapter3.wayBelow_mono le_rfl hcCompact hc.2
        have hContinuous : Chapter2.IsContinuousDomain D.carrier :=
          ⟨CompactElements D, Chapter2.basis_to_raw hAlg⟩
        rcases Chapter2.cor_2_2_16_wayBelow_directed_sup hContinuous hX hs hcs with
          ⟨x, hx, hcx⟩
        exact le_trans ((hpSup x).1 ⟨hc.1, Chapter3.wayBelow_le hcx⟩)
          (hy ⟨x, hx, rfl⟩)
  have hpIdem : ∀ x : D.carrier, pFun (pFun x) = pFun x := by
    intro x
    apply hAnti
    · exact hpMonotone (hpBelow x)
    · exact (hpSup x).2 (pFun (pFun x)) (fun c hc =>
        (hpSup (pFun x)).1 ⟨hc.1, (hpSup x).1 hc⟩)
  let p : KernelOperator D :=
    { toFun := pFun
      continuous := hCont
      idem := hpIdem
      below := hpBelow }
  have hpFixes : KernelOperatorFixes D A p := by
    intro a ha
    have haClosure : a ∈ CompactBasisMubClosureCarrier D A :=
      ⟨hA ha, subset_mubClosure (CompactBasisDomain D) (CompactBasisSubset D A)
        (show (⟨a, hA ha⟩ : (CompactBasisDomain D).carrier) ∈ CompactBasisSubset D A from ha)⟩
    exact hAnti (p.toFun a) a (p.below a) ((hpSup a).1 ⟨haClosure, le_rfl⟩)
  have hpLeast : ∀ q : KernelOperator D, KernelOperatorFixes D A q →
      ∀ x : D.carrier, p.toFun x ≤ q.toFun x := by
    intro q hqFixes
    let Fixed : Set (CompactBasisDomain D).carrier := {c | q.toFun c.1 = c.1}
    have hSourceFixed : CompactBasisSubset D A ⊆ Fixed := by
      intro c hc
      exact hqFixes c.1 hc
    have hFixedClosed : IsMubClosed (CompactBasisDomain D) Fixed := by
      intro M hMfin hMsub m hm
      have hMUpperQ : ∀ c ∈ M, c.1 ≤ q.toFun m.1 := by
        intro c hc
        calc
          c.1 = q.toFun c.1 := (hMsub hc).symm
          _ ≤ q.toFun m.1 := q.continuous.1 (hm.1 hc)
      let values : Set D.carrier := Subtype.val '' M
      have hValuesFin : values.Finite := hMfin.image Subtype.val
      have hWayBelowQ : ∀ c ∈ values, Chapter3.WayBelow c (q.toFun m.1) := by
        intro c hc
        rcases hc with ⟨c, hc, rfl⟩
        exact Chapter3.wayBelow_mono le_rfl c.2 (hMUpperQ c hc)
      rcases Chapter2.finite_wayBelow_basis_upper hAlg hValuesFin hWayBelowQ with
        ⟨b, hb, hMb⟩
      let kb : (CompactBasisDomain D).carrier := ⟨b, hb.1⟩
      have hbLeQ : b ≤ q.toFun m.1 := Chapter3.wayBelow_le hb.2
      have hkbLeM : kb ≤ m := by
        change b ≤ m.1
        exact le_trans hbLeQ (q.below m.1)
      have hmLeB : m ≤ kb := hm.2 (by
        intro c hc
        exact hMb c.1 ⟨c, hc, rfl⟩) hkbLeM
      exact hAnti (q.toFun m.1) m.1 (q.below m.1)
        (le_trans hmLeB (Chapter3.wayBelow_le hb.2))
    intro x
    refine (hpSup x).2 (q.toFun x) ?_
    intro c hc
    rcases hc.1 with ⟨hcCompact, hcClosure⟩
    have hcFixed : (⟨c, hcCompact⟩ : (CompactBasisDomain D).carrier) ∈ Fixed :=
      (Set.mem_sInter.mp hcClosure) Fixed ⟨hSourceFixed, hFixedClosed⟩
    calc
      c = q.toFun c := hcFixed.symm
      _ ≤ q.toFun x := q.continuous.1 hc.2
  exact ⟨p, ⟨⟨hpFixes, hpLeast⟩, hpSup⟩⟩

/-- Idempotent deflations in the sense of Theorem 4.2.6: kernel operators with
finite image.  This is definitionally the same structure as `FiniteProjection`. -/
abbrev IdempotentDeflation (D : OrderedDomain.{u}) : Type u :=
  FiniteProjection D

/-- Finite projections are ordered pointwise. -/
instance finiteProjectionPreorder (D : OrderedDomain.{u}) :
    Preorder (FiniteProjection D) where
  le p q := ∀ x : D.carrier, p.toFun x ≤ q.toFun x
  le_refl p x := le_rfl
  le_trans p q r hpq hqr x := le_trans (hpq x) (hqr x)

/-- Directed idempotent deflations whose pointwise suprema recover the identity. -/
def HasDirectedIdempotentDeflationsApproximatingIdentity (D : OrderedDomain.{u}) : Prop :=
  ∃ P : Set (IdempotentDeflation D),
    P.Nonempty ∧
      (∀ p ∈ P, ∀ q ∈ P,
        ∃ r ∈ P, (∀ x : D.carrier, p.toFun x ≤ r.toFun x ∧ q.toFun x ≤ r.toFun x)) ∧
        ∀ x : D.carrier,
          Chapter3.IsSup ({y : D.carrier | ∃ p ∈ P, y = p.toFun x}) x

/-- The algebraicity direction singled out in the proof of Theorem 4.2.6:
a directed family of finite-image kernel operators with pointwise supremum the
identity supplies a compact basis. -/
theorem algebraic_of_directed_idempotentDeflations
    (D : OrderedDomain.{u})
    (hD : HasDirectedIdempotentDeflationsApproximatingIdentity D) :
    Chapter3.IsAlgebraicDomain D.carrier := by
  rcases hD with ⟨P, hPnonempty, hPdirected, hPsup⟩
  apply Chapter2.prop_2_2_4_1
  intro x
  let approximatingImages : Set D.carrier :=
    {y | ∃ p ∈ P, y = p.toFun x}
  refine ⟨approximatingImages, ?_, ?_, hPsup x⟩
  · intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    have hpCompact : Chapter3.Compact (p.toFun x) :=
      p.compact_of_mem_range ⟨x, rfl⟩
    exact ⟨hpCompact,
      Chapter3.wayBelow_mono le_rfl hpCompact (p.below x)⟩
  · constructor
    · rcases hPnonempty with ⟨p, hp⟩
      exact ⟨p.toFun x, ⟨p, hp, rfl⟩⟩
    · intro y hy z hz
      rcases hy with ⟨p, hp, rfl⟩
      rcases hz with ⟨q, hq, rfl⟩
      rcases hPdirected p hp q hq with ⟨r, hr, hprq⟩
      exact ⟨r.toFun x, ⟨r, hr, rfl⟩, (hprq x).1, (hprq x).2⟩

/-- A finite family of compact elements is fixed by one member of any directed
family of finite projections whose pointwise supremum is the identity. -/
theorem exists_idempotentDeflation_fixing_finite_compacts
    (D : OrderedDomain.{u})
    (hAnti : ∀ x y : D.carrier, x ≤ y → y ≤ x → x = y)
    {P : Set (IdempotentDeflation D)}
    (hPnonempty : P.Nonempty)
    (hPdirected : ∀ p ∈ P, ∀ q ∈ P,
      ∃ r ∈ P, ∀ x : D.carrier,
        p.toFun x ≤ r.toFun x ∧ q.toFun x ≤ r.toFun x)
    (hPsup : ∀ x : D.carrier,
      Chapter3.IsSup ({y : D.carrier | ∃ p ∈ P, y = p.toFun x}) x)
    {A : Set D.carrier} (hAfin : A.Finite)
    (hAcompact : A ⊆ CompactElements D) :
    ∃ p ∈ P, ProjectionFixes D A p := by
  classical
  have hPDirectedSet : Chapter3.DirectedSet P := by
    constructor
    · exact hPnonempty
    · intro p hp q hq
      rcases hPdirected p hp q hq with ⟨r, hr, hprq⟩
      exact ⟨r, hr, fun x => (hprq x).1, fun x => (hprq x).2⟩
  have hEach : ∀ a ∈ A, ∃ p ∈ P, p.toFun a = a := by
    intro a ha
    let values : Set D.carrier := {y | ∃ p ∈ P, y = p.toFun a}
    have hValuesDirected : Chapter3.DirectedSet values := by
      constructor
      · rcases hPnonempty with ⟨p, hp⟩
        exact ⟨p.toFun a, ⟨p, hp, rfl⟩⟩
      · intro x hx y hy
        rcases hx with ⟨p, hp, rfl⟩
        rcases hy with ⟨q, hq, rfl⟩
        rcases hPdirected p hp q hq with ⟨r, hr, hprq⟩
        exact ⟨r.toFun a, ⟨r, hr, rfl⟩, (hprq a).1, (hprq a).2⟩
    rcases (hAcompact ha) hValuesDirected (hPsup a) le_rfl with
      ⟨y, hy, hay⟩
    rcases hy with ⟨p, hp, rfl⟩
    exact ⟨p, hp, hAnti (p.toFun a) a (p.below a) hay⟩
  let pick : {a // a ∈ A} → IdempotentDeflation D := fun a =>
    Classical.choose (hEach a.1 a.2)
  have hPickMem : ∀ a : {a // a ∈ A}, pick a ∈ P := fun a =>
    (Classical.choose_spec (hEach a.1 a.2)).1
  have hPickFix : ∀ a : {a // a ∈ A}, (pick a).toFun a.1 = a.1 := fun a =>
    (Classical.choose_spec (hEach a.1 a.2)).2
  letI : Fintype {a // a ∈ A} := hAfin.fintype
  let chosen : Set (IdempotentDeflation D) := Set.range pick
  have hChosenFinite : chosen.Finite := Set.finite_range pick
  have hChosenSub : chosen ⊆ P := by
    intro p hp
    rcases hp with ⟨a, rfl⟩
    exact hPickMem a
  rcases Chapter2.DirectedSet.exists_upper_finite hPDirectedSet hChosenFinite hChosenSub with
    ⟨p, hp, hpUpper⟩
  refine ⟨p, hp, ?_⟩
  intro a ha
  let a' : {a // a ∈ A} := ⟨a, ha⟩
  exact hAnti (p.toFun a) a (p.below a) (by
    calc
      a = (pick a').toFun a := (hPickFix a').symm
      _ ≤ p.toFun a := hpUpper (pick a') ⟨a', rfl⟩ a)

/-- In an algebraic domain, a finite projection fixing `A` also fixes the
compact-basis mub-closure of `A`; hence that closure lies in its finite range. -/
theorem mubClosure_subset_projection_range
    (D : OrderedDomain.{u})
    (hAnti : ∀ x y : D.carrier, x ≤ y → y ≤ x → x = y)
    (hAlg : Chapter3.IsAlgebraicDomain D.carrier)
    (A : Set D.carrier) (p : FiniteProjection D)
    (hpFixes : ProjectionFixes D A p) :
    MubClosure (CompactBasisDomain D) (CompactBasisSubset D A) ⊆
      {c : (CompactBasisDomain D).carrier | c.1 ∈ Set.range p.toFun} := by
  classical
  let Fixed : Set (CompactBasisDomain D).carrier := {c | p.toFun c.1 = c.1}
  have hSourceFixed : CompactBasisSubset D A ⊆ Fixed := by
    intro c hc
    exact hpFixes c.1 hc
  have hFixedClosed : IsMubClosed (CompactBasisDomain D) Fixed := by
    intro M hMfin hMsub m hm
    have hMUpperP : ∀ c ∈ M, c.1 ≤ p.toFun m.1 := by
      intro c hc
      calc
        c.1 = p.toFun c.1 := (hMsub hc).symm
        _ ≤ p.toFun m.1 := p.continuous.1 (hm.1 hc)
    let values : Set D.carrier := Subtype.val '' M
    have hValuesFin : values.Finite := hMfin.image Subtype.val
    have hWayBelowP : ∀ c ∈ values, Chapter3.WayBelow c (p.toFun m.1) := by
      intro c hc
      rcases hc with ⟨c, hc, rfl⟩
      exact Chapter3.wayBelow_mono le_rfl c.2 (hMUpperP c hc)
    rcases Chapter2.finite_wayBelow_basis_upper hAlg hValuesFin hWayBelowP with
      ⟨b, hb, hMb⟩
    let kb : (CompactBasisDomain D).carrier := ⟨b, hb.1⟩
    have hkbLeM : kb ≤ m := by
      change b ≤ m.1
      exact le_trans (Chapter3.wayBelow_le hb.2) (p.below m.1)
    have hmLeB : m ≤ kb := hm.2 (by
      intro c hc
      exact hMb c.1 ⟨c, hc, rfl⟩) hkbLeM
    exact hAnti (p.toFun m.1) m.1 (p.below m.1)
      (le_trans hmLeB (Chapter3.wayBelow_le hb.2))
  intro c hc
  have hcFixed : c ∈ Fixed :=
    (Set.mem_sInter.mp hc) Fixed ⟨hSourceFixed, hFixedClosed⟩
  exact ⟨c.1, hcFixed⟩

/-- The compact basis of a pointed dcpo approximated by directed finite
projections is a Plotkin order. -/
theorem plotkinOrder_of_directed_idempotentDeflations
    (D : OrderedDomain.{u})
    (hAnti : ∀ x y : D.carrier, x ≤ y → y ≤ x → x = y)
    (hBottom : HasBottom D)
    (hDefl : HasDirectedIdempotentDeflationsApproximatingIdentity D) :
    IsPlotkinOrder (CompactBasisDomain D) := by
  classical
  rcases hDefl with ⟨P, hPnonempty, hPdirected, hPsup⟩
  have hAlg : Chapter3.IsAlgebraicDomain D.carrier :=
    algebraic_of_directed_idempotentDeflations D ⟨P, hPnonempty, hPdirected, hPsup⟩
  have hMubComplete : IsMubComplete (CompactBasisDomain D) := by
    intro M hMfin u hu
    let values : Set D.carrier := Subtype.val '' M
    have hValuesFin : values.Finite := hMfin.image Subtype.val
    have hValuesCompact : values ⊆ CompactElements D := by
      intro c hc
      rcases hc with ⟨c, _hc, rfl⟩
      exact c.2
    rcases exists_idempotentDeflation_fixing_finite_compacts D hAnti
        hPnonempty hPdirected hPsup hValuesFin hValuesCompact with
      ⟨p, hpP, hpFixes⟩
    let pu : (CompactBasisDomain D).carrier :=
      ⟨p.toFun u.1, p.compact_of_mem_range ⟨u.1, rfl⟩⟩
    have hPuUpper : Chapter3.IsUpperBound M pu := by
      intro c hc
      calc
        c.1 = p.toFun c.1 := (hpFixes c.1 ⟨c, hc, rfl⟩).symm
        _ ≤ p.toFun u.1 := p.continuous.1 (hu hc)
    let candidates : Set (CompactBasisDomain D).carrier :=
      {c | c.1 ∈ Set.range p.toFun ∧ Chapter3.IsUpperBound M c ∧ c ≤ pu}
    have hCandidatesFinite : candidates.Finite := by
      apply Set.Finite.of_finite_image (f := Subtype.val)
      · exact p.finite_range.subset (by
          intro c hc
          rcases hc with ⟨c, hc, rfl⟩
          exact hc.1)
      · exact Subtype.val_injective.injOn
    have hPuCandidate : pu ∈ candidates :=
      ⟨⟨u.1, rfl⟩, hPuUpper, le_rfl⟩
    rcases hCandidatesFinite.exists_le_minimal hPuCandidate with
      ⟨m, hmLePu, hmMinimal⟩
    refine ⟨m, ⟨hmMinimal.1.2.1, ?_⟩, le_trans hmLePu (p.below u.1)⟩
    intro y hyUpper hym
    let py : (CompactBasisDomain D).carrier :=
      ⟨p.toFun y.1, p.compact_of_mem_range ⟨y.1, rfl⟩⟩
    have hPyUpper : Chapter3.IsUpperBound M py := by
      intro c hc
      calc
        c.1 = p.toFun c.1 := (hpFixes c.1 ⟨c, hc, rfl⟩).symm
        _ ≤ p.toFun y.1 := p.continuous.1 (hyUpper hc)
    have hPyLeM : py ≤ m := le_trans (p.below y.1) hym
    have hPyCandidate : py ∈ candidates := by
      refine ⟨⟨y.1, rfl⟩, hPyUpper, ?_⟩
      exact le_trans hPyLeM hmLePu
    exact le_trans (hmMinimal.2 hPyCandidate hPyLeM) (p.below y.1)
  have hFiniteClosure : HasFiniteMubClosureProperty (CompactBasisDomain D) := by
    intro A hAfin
    let values : Set D.carrier := Subtype.val '' A
    have hValuesFin : values.Finite := hAfin.image Subtype.val
    have hValuesCompact : values ⊆ CompactElements D := by
      intro c hc
      rcases hc with ⟨c, _hc, rfl⟩
      exact c.2
    rcases exists_idempotentDeflation_fixing_finite_compacts D hAnti
        hPnonempty hPdirected hPsup hValuesFin hValuesCompact with
      ⟨p, _hpP, hpFixes⟩
    have hSourceEq : CompactBasisSubset D values = A := by
      ext c
      constructor
      · rintro ⟨a, ha, hEq⟩
        exact Subtype.val_injective hEq ▸ ha
      · intro hc
        exact ⟨c, hc, rfl⟩
    have hClosureRange :
        MubClosure (CompactBasisDomain D) A ⊆
          {c : (CompactBasisDomain D).carrier | c.1 ∈ Set.range p.toFun} := by
      rw [← hSourceEq]
      exact mubClosure_subset_projection_range D hAnti hAlg values p hpFixes
    apply Set.Finite.of_finite_image (f := Subtype.val)
    · exact p.finite_range.subset (by
        intro c hc
        rcases hc with ⟨c, hc, rfl⟩
        exact hClosureRange hc)
    · exact Subtype.val_injective.injOn
  rcases hBottom with ⟨bot, hbot⟩
  have hBotCompact : Chapter3.Compact bot := by
    intro A s hA _hs _hbotS
    rcases hA.1 with ⟨a, ha⟩
    exact ⟨a, ha, hbot a⟩
  have hCompactBottom : HasBottom (CompactBasisDomain D) :=
    ⟨⟨bot, hBotCompact⟩, fun c => hbot c.1⟩
  exact ⟨⟨hMubComplete, hFiniteClosure⟩, hCompactBottom⟩

/-- Proposition 4.2.5 yields a finite projection when the relevant compact-basis
mub-closure is finite.  Finiteness of the range follows because every value is
the unique supremum of one of finitely many subsets of that closure. -/
theorem exists_finiteProjection_generatedBy_finite_mubClosure
    (D : OrderedDomain.{u})
    (hDcpo : Chapter3.IsDcpo D.carrier)
    (hAnti : ∀ x y : D.carrier, x ≤ y → y ≤ x → x = y)
    (hAlg : Chapter3.IsAlgebraicDomain D.carrier)
    (hMub : IsMubComplete (CompactBasisDomain D))
    (hBottom : HasBottom D)
    (A : Set D.carrier) (hA : A ⊆ CompactElements D)
    (hClosureFinite :
      (MubClosure (CompactBasisDomain D) (CompactBasisSubset D A)).Finite) :
    ∃ p : FiniteProjection D,
      IsLeastKernelOperatorFixing D A (FiniteProjection.toKernelOperator p) ∧
        KernelOperatorGeneratedByMubClosure D A
          (FiniteProjection.toKernelOperator p) := by
  classical
  rcases prop_4_2_5_mub_complete_basis_bifinite D hDcpo hAnti hAlg hMub A hA with
    ⟨p, hpLeast, hpGenerated⟩
  let closureCarrier : Set D.carrier := CompactBasisMubClosureCarrier D A
  have hClosureCarrierFinite : closureCarrier.Finite := by
    have hEq : closureCarrier =
        Subtype.val '' MubClosure (CompactBasisDomain D) (CompactBasisSubset D A) := by
      ext c
      constructor
      · rintro ⟨hc, hcmc⟩
        exact ⟨⟨c, hc⟩, hcmc, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨c.2, hc⟩
    rw [hEq]
    exact hClosureFinite.image Subtype.val
  let sections : Set (Set D.carrier) := {S | S ⊆ closureCarrier}
  have hSectionsFinite : sections.Finite := hClosureCarrierFinite.finite_subsets
  rcases hBottom with ⟨bot, _hbot⟩
  let chosenSup : Set D.carrier → D.carrier := fun S =>
    if hS : ∃ z : D.carrier, Chapter3.IsSup S z then Classical.choose hS else bot
  have hpRangeSub : Set.range p.toFun ⊆ chosenSup '' sections := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    let Sx : Set D.carrier :=
      {c | c ∈ CompactBasisMubClosureCarrier D A ∧ c ≤ x}
    have hSxSection : Sx ∈ sections := by
      intro c hc
      exact hc.1
    have hSxSup : Chapter3.IsSup Sx (p.toFun x) := hpGenerated x
    have hChosenSpec : Chapter3.IsSup Sx (chosenSup Sx) := by
      dsimp [chosenSup]
      rw [dif_pos ⟨p.toFun x, hSxSup⟩]
      exact Classical.choose_spec ⟨p.toFun x, hSxSup⟩
    exact ⟨Sx, hSxSection, hAnti _ _
      (hChosenSpec.2 (p.toFun x) hSxSup.1)
      (hSxSup.2 (chosenSup Sx) hChosenSpec.1)⟩
  have hpRangeFinite : (Set.range p.toFun).Finite :=
    (hSectionsFinite.image chosenSup).subset hpRangeSub
  let q : FiniteProjection D :=
    { toFun := p.toFun
      continuous := p.continuous
      idem := p.idem
      below := p.below
      finite_range := hpRangeFinite }
  exact ⟨q, hpLeast, hpGenerated⟩

/-- A bifinite compact basis generates a directed family of finite projections
whose pointwise supremum is the identity. -/
theorem directed_idempotentDeflations_of_bifinite
    (D : OrderedDomain.{u})
    (hDcpo : Chapter3.IsDcpo D.carrier)
    (hAnti : ∀ x y : D.carrier, x ≤ y → y ≤ x → x = y)
    (hBottom : HasBottom D)
    (hBif : HasBifiniteCompactBasis D) :
    HasDirectedIdempotentDeflationsApproximatingIdentity D := by
  classical
  let FiniteCompactSets :=
    {K : Set (CompactBasisDomain D).carrier // K.Finite}
  let values : FiniteCompactSets → Set D.carrier := fun K => Subtype.val '' K.1
  have hValuesCompact : ∀ K : FiniteCompactSets, values K ⊆ CompactElements D := by
    intro K c hc
    rcases hc with ⟨c, _hc, rfl⟩
    exact c.2
  have hSourceEq : ∀ K : FiniteCompactSets, CompactBasisSubset D (values K) = K.1 := by
    intro K
    ext c
    constructor
    · rintro ⟨a, ha, hEq⟩
      exact Subtype.val_injective hEq ▸ ha
    · intro hc
      exact ⟨c, hc, rfl⟩
  have hProjectionExists : ∀ K : FiniteCompactSets,
      ∃ p : FiniteProjection D,
        IsLeastKernelOperatorFixing D (values K) (FiniteProjection.toKernelOperator p) ∧
          KernelOperatorGeneratedByMubClosure D (values K)
            (FiniteProjection.toKernelOperator p) := by
    intro K
    apply exists_finiteProjection_generatedBy_finite_mubClosure
      D hDcpo hAnti hBif.1 hBif.2.1.1 hBottom (values K) (hValuesCompact K)
    rw [hSourceEq K]
    exact hBif.2.1.2 K.1 K.2
  let projectionFor : FiniteCompactSets → FiniteProjection D := fun K =>
    Classical.choose (hProjectionExists K)
  have hProjectionSpec : ∀ K : FiniteCompactSets,
      IsLeastKernelOperatorFixing D (values K)
          (FiniteProjection.toKernelOperator (projectionFor K)) ∧
        KernelOperatorGeneratedByMubClosure D (values K)
          (FiniteProjection.toKernelOperator (projectionFor K)) := fun K =>
    Classical.choose_spec (hProjectionExists K)
  let P : Set (IdempotentDeflation D) := Set.range projectionFor
  refine ⟨P, ?_, ?_, ?_⟩
  · let emptyK : FiniteCompactSets := ⟨∅, Set.finite_empty⟩
    exact ⟨projectionFor emptyK, ⟨emptyK, rfl⟩⟩
  · intro p hp q hq
    rcases hp with ⟨K, rfl⟩
    rcases hq with ⟨L, rfl⟩
    let unionK : FiniteCompactSets := ⟨K.1 ∪ L.1, K.2.union L.2⟩
    let r := projectionFor unionK
    have hrP : r ∈ P := ⟨unionK, rfl⟩
    have hrFixUnion : ProjectionFixes D (values unionK) r :=
      (hProjectionSpec unionK).1.1
    have hrFixK : ProjectionFixes D (values K) r := by
      intro c hc
      exact hrFixUnion c (by
        rcases hc with ⟨k, hk, rfl⟩
        exact ⟨k, Or.inl hk, rfl⟩)
    have hrFixL : ProjectionFixes D (values L) r := by
      intro c hc
      exact hrFixUnion c (by
        rcases hc with ⟨k, hk, rfl⟩
        exact ⟨k, Or.inr hk, rfl⟩)
    exact ⟨r, hrP, fun x =>
      ⟨(hProjectionSpec K).1.2 (FiniteProjection.toKernelOperator r) hrFixK x,
        (hProjectionSpec L).1.2 (FiniteProjection.toKernelOperator r) hrFixL x⟩⟩
  · intro x
    constructor
    · intro y hy
      rcases hy with ⟨p, _hp, rfl⟩
      exact p.below x
    · intro y hy
      exact (hBif.1 x).2.2 y (by
        intro c hc
        let kc : (CompactBasisDomain D).carrier := ⟨c, hc.1⟩
        let singletonK : FiniteCompactSets :=
          ⟨({kc} : Set (CompactBasisDomain D).carrier), Set.finite_singleton kc⟩
        let p := projectionFor singletonK
        have hpP : p ∈ P := ⟨singletonK, rfl⟩
        have hcValues : c ∈ values singletonK := by
          change c ∈ Subtype.val '' ({kc} : Set (CompactBasisDomain D).carrier)
          exact ⟨kc, rfl, rfl⟩
        have hpFix : p.toFun c = c :=
          (hProjectionSpec singletonK).1.1 c hcValues
        calc
          c = p.toFun c := hpFix.symm
          _ ≤ p.toFun x := p.continuous.1 (Chapter3.wayBelow_le hc.2)
          _ ≤ y := hy ⟨p, hpP, rfl⟩)

/-- Backwards-compatible name for the directed finite-projection formulation. -/
abbrev HasDirectedFiniteProjectionsApproximatingIdentity (D : OrderedDomain.{u}) : Prop :=
  HasDirectedIdempotentDeflationsApproximatingIdentity D

/-- The PDF's all-idempotent-deflations characterization: the collection of all
idempotent deflations is directed and has pointwise supremum the identity. -/
def HasAllFiniteDeflationsApproximatingIdentity (D : OrderedDomain.{u}) : Prop :=
  (Set.univ : Set (IdempotentDeflation D)).Nonempty ∧
    (∀ p : IdempotentDeflation D, ∀ q : IdempotentDeflation D,
      ∃ r : IdempotentDeflation D,
        ∀ x : D.carrier, p.toFun x ≤ r.toFun x ∧ q.toFun x ≤ r.toFun x) ∧
      ∀ x : D.carrier,
        Chapter3.IsSup ({y : D.carrier | ∃ p : IdempotentDeflation D, y = p.toFun x}) x

/-- A directed approximating family makes the collection of all finite
projections directed: choose one family member fixing the finite union of the
two ranges. -/
theorem all_idempotentDeflations_of_directed
    (D : OrderedDomain.{u})
    (hAnti : ∀ x y : D.carrier, x ≤ y → y ≤ x → x = y)
    (hDefl : HasDirectedIdempotentDeflationsApproximatingIdentity D) :
    HasAllFiniteDeflationsApproximatingIdentity D := by
  classical
  rcases hDefl with ⟨P, hPnonempty, hPdirected, hPsup⟩
  constructor
  · rcases hPnonempty with ⟨p, _hp⟩
    exact ⟨p, Set.mem_univ p⟩
  constructor
  · intro p q
    let ranges : Set D.carrier := Set.range p.toFun ∪ Set.range q.toFun
    have hRangesFinite : ranges.Finite := p.finite_range.union q.finite_range
    have hRangesCompact : ranges ⊆ CompactElements D := by
      intro y hy
      rcases hy with hy | hy
      · exact p.compact_of_mem_range hy
      · exact q.compact_of_mem_range hy
    rcases exists_idempotentDeflation_fixing_finite_compacts D hAnti
        hPnonempty hPdirected hPsup hRangesFinite hRangesCompact with
      ⟨r, _hrP, hrFixes⟩
    refine ⟨r, fun x => ⟨?_, ?_⟩⟩
    · calc
        p.toFun x = r.toFun (p.toFun x) :=
          (hrFixes (p.toFun x) (Or.inl ⟨x, rfl⟩)).symm
        _ ≤ r.toFun x := r.continuous.1 (p.below x)
    · calc
        q.toFun x = r.toFun (q.toFun x) :=
          (hrFixes (q.toFun x) (Or.inr ⟨x, rfl⟩)).symm
        _ ≤ r.toFun x := r.continuous.1 (q.below x)
  · intro x
    constructor
    · intro y hy
      rcases hy with ⟨p, rfl⟩
      exact p.below x
    · intro y hy
      exact (hPsup x).2 y (by
        intro z hz
        rcases hz with ⟨p, hp, rfl⟩
        exact hy ⟨p, rfl⟩)

/-- The all-deflations formulation contains the directed-family formulation by
taking the family to be the universal set. -/
theorem directed_idempotentDeflations_of_all
    (D : OrderedDomain.{u})
    (hAll : HasAllFiniteDeflationsApproximatingIdentity D) :
    HasDirectedIdempotentDeflationsApproximatingIdentity D := by
  rcases hAll with ⟨hNonempty, hDirected, hSup⟩
  refine ⟨Set.univ, hNonempty, ?_, ?_⟩
  · intro p _hp q _hq
    rcases hDirected p q with ⟨r, hprq⟩
    exact ⟨r, Set.mem_univ r, hprq⟩
  · intro x
    simpa using hSup x

/-- Theorem 4.2.6 statement package. PDF text: for a pointed dcpo `D`, the
following are equivalent: `D` is a bifinite domain; there is a directed
collection of idempotent deflations with supremum `id_D`; and the set of all
idempotent deflations is directed with join `id_D`.

Here the first item uses the compact-basis definition from Definition 4.2.1,
not the sequence-style `IsBifiniteObject` compatibility predicate. -/
def BifiniteFunctionalCharacterizations (D : OrderedDomain.{u}) : Prop :=
  (HasBifiniteCompactBasis D ↔ HasDirectedIdempotentDeflationsApproximatingIdentity D) ∧
    (HasBifiniteCompactBasis D ↔ HasAllFiniteDeflationsApproximatingIdentity D)

/-- Theorem 4.2.6, PDF text: for a pointed dcpo, compact-basis bifiniteness is
equivalent to the directed and all-idempotent-deflation characterizations.  The
proof constructs finite projections from finite mub-closures and reconstructs
the Plotkin-order conditions from any directed approximating family. -/
theorem theorem_4_2_6_bifinite_functional_characterizations
    (D : OrderedDomain.{u}) (hDcpo : Chapter3.IsDcpo D.carrier)
    (hAnti : ∀ x y : D.carrier, x ≤ y → y ≤ x → x = y)
    (hD : HasBottom D) :
    BifiniteFunctionalCharacterizations D := by
  have hBifDirected :
      HasBifiniteCompactBasis D ↔
        HasDirectedIdempotentDeflationsApproximatingIdentity D := by
    constructor
    · exact directed_idempotentDeflations_of_bifinite D hDcpo hAnti hD
    · intro hDefl
      exact ⟨algebraic_of_directed_idempotentDeflations D hDefl,
        plotkinOrder_of_directed_idempotentDeflations D hAnti hD hDefl⟩
  have hDirectedAll :
      HasDirectedIdempotentDeflationsApproximatingIdentity D ↔
        HasAllFiniteDeflationsApproximatingIdentity D := by
    constructor
    · exact all_idempotentDeflations_of_directed D hAnti
    · exact directed_idempotentDeflations_of_all D
  exact ⟨hBifDirected, hBifDirected.trans hDirectedAll⟩

/-- The general directed-system form of the bilimit criterion used in Lemma
3.3.8.  Every stage is represented by an e-p pair into the bilimit object.  The
`nested` law says that the image at an earlier index is contained in every
later image, and `approximates` says that the induced kernel operators have
pointwise supremum the identity.

Unlike `Chapter3.ExpandingSequence`, the index type here is arbitrary.  This is
essential in Theorem 4.2.7: restricting the index to `Nat` would describe only
the countably based bifinite domains mentioned after that theorem in the PDF. -/
structure FinitePointedExpandingBilimit (D : OrderedDomain.{u}) where
  Index : Type u
  indexPreorder : Preorder Index
  indexNonempty : Nonempty Index
  indexDirected : ∀ i j : Index, ∃ k : Index, i ≤ k ∧ j ≤ k
  Stage : Index → Type u
  stagePreorder : ∀ i : Index, Preorder (Stage i)
  stageFinite : ∀ i : Index, (Set.univ : Set (Stage i)).Finite
  stageAntisymm : ∀ i : Index, ∀ x y : Stage i, x ≤ y → y ≤ x → x = y
  stageBottom : ∀ i : Index, ∃ bot : Stage i, ∀ x : Stage i, bot ≤ x
  stageEP : ∀ i : Index, Chapter3.EPPair (Stage i) D.carrier
  nested : ∀ {i j : Index}, i ≤ j → ∀ x : Stage i,
    (stageEP j).e ((stageEP j).p ((stageEP i).e x)) = (stageEP i).e x
  approximates : ∀ x : D.carrier,
    Chapter3.IsSup
      ({y : D.carrier | ∃ i : Index,
        y = (stageEP i).e ((stageEP i).p x)} : Set D.carrier) x
  limitBottom : HasBottom D

namespace FinitePointedExpandingBilimit

variable {D : OrderedDomain.{u}}

instance (B : FinitePointedExpandingBilimit D) : Preorder B.Index :=
  B.indexPreorder

instance (B : FinitePointedExpandingBilimit D) (i : B.Index) :
    Preorder (B.Stage i) := B.stagePreorder i

/-- The kernel operator on the bilimit induced by one finite stage. -/
def inducedKernel (B : FinitePointedExpandingBilimit D) (i : B.Index) :
    Chapter3.KernelOperator D.carrier where
  k := fun x => (B.stageEP i).e ((B.stageEP i).p x)
  continuous := (B.stageEP i).continuous_e.comp (B.stageEP i).continuous_p
  idem := by
    intro x
    rw [(B.stageEP i).retract]
  below := (B.stageEP i).below

/-- Earlier stage kernels lie pointwise below later stage kernels. -/
theorem inducedKernel_mono (B : FinitePointedExpandingBilimit D)
    {i j : B.Index} (hij : i ≤ j) (x : D.carrier) :
    (B.inducedKernel i).k x ≤ (B.inducedKernel j).k x := by
  calc
    (B.inducedKernel i).k x =
        (B.stageEP j).e ((B.stageEP j).p ((B.inducedKernel i).k x)) := by
          exact (B.nested hij ((B.stageEP i).p x)).symm
    _ ≤ (B.stageEP j).e ((B.stageEP j).p x) :=
      (B.stageEP j).continuous_e.1
        ((B.stageEP j).continuous_p.1 ((B.stageEP i).below x))
    _ = (B.inducedKernel j).k x := rfl

/-- A finite stage gives a finite-image projection on the bilimit. -/
def inducedFiniteProjection (B : FinitePointedExpandingBilimit D)
    (i : B.Index) : FiniteProjection D where
  toFun := (B.inducedKernel i).k
  continuous := (B.inducedKernel i).continuous
  idem := (B.inducedKernel i).idem
  below := (B.inducedKernel i).below
  finite_range := by
    apply (B.stageFinite i).image (B.stageEP i).e |>.subset
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact ⟨(B.stageEP i).p x, Set.mem_univ _, rfl⟩

/-- The directed finite-stage presentation yields the functional family from
Theorem 4.2.6. -/
theorem hasDirectedIdempotentDeflations
    (B : FinitePointedExpandingBilimit D) :
    HasDirectedIdempotentDeflationsApproximatingIdentity D := by
  let P : Set (IdempotentDeflation D) := Set.range B.inducedFiniteProjection
  refine ⟨P, ?_, ?_, ?_⟩
  · rcases B.indexNonempty with ⟨i⟩
    exact ⟨B.inducedFiniteProjection i, ⟨i, rfl⟩⟩
  · intro p hp q hq
    rcases hp with ⟨i, rfl⟩
    rcases hq with ⟨j, rfl⟩
    rcases B.indexDirected i j with ⟨k, hik, hjk⟩
    exact ⟨B.inducedFiniteProjection k, ⟨k, rfl⟩,
      fun x => ⟨B.inducedKernel_mono hik x, B.inducedKernel_mono hjk x⟩⟩
  · intro x
    simpa [P, inducedFiniteProjection, inducedKernel] using B.approximates x

end FinitePointedExpandingBilimit

/-- A dcpo is a bilimit of an expanding system of finite pointed posets when
it carries a general directed finite-stage presentation satisfying the
Lemma 3.3.8 pointwise-supremum criterion. -/
def IsBilimitOfFinitePointedPosets (D : OrderedDomain.{u}) : Prop :=
  Nonempty (FinitePointedExpandingBilimit D)

/-- The compact-basis definition of bifiniteness supplies a least element of
the ambient dcpo from the least compact element. -/
theorem hasBottom_of_bifiniteCompactBasis
    (D : OrderedDomain.{u}) (hBif : HasBifiniteCompactBasis D) : HasBottom D := by
  rcases hBif.2.2 with ⟨bot, hbot⟩
  refine ⟨bot.1, ?_⟩
  intro x
  have hBasis : Chapter2.IsBasis (CompactElements D) := by
    simpa [CompactElements, Chapter2.CompactSet] using hBif.1
  rcases (hBasis x).1.1 with ⟨c, hcCompact, hcx⟩
  exact le_trans (hbot ⟨c, hcCompact⟩) (Chapter3.wayBelow_le hcx)

/-- Turn one finite projection into its finite kernel-image stage. -/
def finiteProjectionKernel (D : OrderedDomain.{u}) (p : FiniteProjection D) :
    Chapter3.KernelOperator D.carrier where
  k := p.toFun
  continuous := p.continuous
  idem := p.idem
  below := p.below

/-- Theorem 4.2.7, PDF text: a dcpo is bifinite iff it is a bilimit of an
expanding system of finite pointed posets.  The forward direction takes the
finite kernel images of the directed deflations from Theorem 4.2.6; the reverse
direction composes each stage projection with its embedding and invokes the
same functional characterization. -/
theorem theorem_4_2_7_bifinite_iff_bilimit_finite_posets
    (D : OrderedDomain.{u}) (hDcpo : Chapter3.IsDcpo D.carrier)
    (hAnti : ∀ x y : D.carrier, x ≤ y → y ≤ x → x = y) :
    HasBifiniteCompactBasis D ↔ IsBilimitOfFinitePointedPosets D := by
  constructor
  · intro hBif
    let hBottom : HasBottom D := hasBottom_of_bifiniteCompactBasis D hBif
    have hDefl : HasDirectedIdempotentDeflationsApproximatingIdentity D :=
      (theorem_4_2_6_bifinite_functional_characterizations
        D hDcpo hAnti hBottom).1.mp hBif
    rcases hDefl with ⟨P, hPnonempty, hPdirected, hPsup⟩
    let I := {p : IdempotentDeflation D // p ∈ P}
    let K : I → Chapter3.KernelOperator D.carrier := fun p =>
      finiteProjectionKernel D p.1
    let X : I → Type u := fun p => (K p).ImageCarrier
    let instX : ∀ p : I, Preorder (X p) := fun p => (K p).imageCarrierPreorder
    let ep : ∀ p : I, Chapter3.EPPair (X p) D.carrier := fun p =>
      { e := (K p).inclusion
        p := (K p).projection
        continuous_e := (K p).inclusion_scottContinuous
        continuous_p := (K p).projection_scottContinuous
        retract := (K p).projection_inclusion_eq
        below := (K p).below }
    refine ⟨{
      Index := I
      indexPreorder := inferInstance
      indexNonempty := by
        rcases hPnonempty with ⟨p, hp⟩
        exact ⟨⟨p, hp⟩⟩
      indexDirected := by
        intro p q
        rcases hPdirected p.1 p.2 q.1 q.2 with ⟨r, hr, hprq⟩
        exact ⟨⟨r, hr⟩, fun x => (hprq x).1, fun x => (hprq x).2⟩
      Stage := X
      stagePreorder := instX
      stageFinite := by
        intro p
        letI : Preorder (X p) := instX p
        letI : Fintype (X p) := p.1.finite_range.fintype
        exact Set.toFinite _
      stageAntisymm := by
        intro p x y hxy hyx
        apply Subtype.ext
        exact hAnti x.1 y.1 hxy hyx
      stageBottom := by
        intro p
        letI : Preorder (X p) := instX p
        rcases hBottom with ⟨bot, hbot⟩
        refine ⟨(K p).projection bot, ?_⟩
        intro x
        change (K p).k bot ≤ x.1
        exact le_trans ((K p).below bot) (hbot x.1)
      stageEP := ep
      nested := by
        intro p q hpq x
        change q.1.toFun x.1 = x.1
        apply hAnti
        · exact q.1.below x.1
        · calc
            x.1 = p.1.toFun x.1 := ((K p).mem_range_iff_fixed.mp x.2).symm
            _ ≤ q.1.toFun x.1 := hpq x.1
      approximates := by
        intro x
        change Chapter3.IsSup
          ({y : D.carrier | ∃ p : I, y = p.1.toFun x} : Set D.carrier) x
        simpa [I] using hPsup x
      limitBottom := hBottom }⟩
  · rintro ⟨B⟩
    exact (theorem_4_2_6_bifinite_functional_characterizations
      D hDcpo hAnti B.limitBottom).1.mpr B.hasDirectedIdempotentDeflations

/-- Closure of a class under coalesced sums, represented by an object whose
carrier is order-isomorphic to the coalesced-sum carrier from Chapter 3. -/
def DomainClass.ClosedUnderCoalescedSums (C : DomainClass.{u}) : Prop :=
  ∀ D E : OrderedDomain.{u}, ∀ [OrderBot D.carrier], ∀ [OrderBot E.carrier],
    C.Obj D → C.Obj E →
      ∃ S : OrderedDomain.{u},
        C.Obj S ∧
          Nonempty (Chapter3.OrderIsoData S.carrier (Chapter3.CoalescedSum D.carrier E.carrier))

/-- Closure of a class under bilimits of expanding sequences whose stages are in
the class, represented by order-isomorphism data. -/
def DomainClass.ClosedUnderExpandingBilimits (C : DomainClass.{u}) : Prop :=
  ∀ (X : Nat → Type u) (inst : ∀ n : Nat, Preorder (X n)),
    letI := inst
    ∀ S : Chapter3.ExpandingSequence X,
      (∀ n : Nat, ∃ Dn : OrderedDomain.{u},
        C.Obj Dn ∧ Nonempty (Chapter3.OrderIsoData Dn.carrier (X n))) →
        ∃ B : OrderedDomain.{u},
          C.Obj B ∧ Nonempty (Chapter3.OrderIsoData B.carrier (Chapter3.Bilimit S))

namespace FiniteProjection

/-- Product of two finite projections, acting coordinatewise. -/
def prod {D E : OrderedDomain.{u}} (p : FiniteProjection D)
    (q : FiniteProjection E) : FiniteProjection (OrderedDomain.prod D E) where
  toFun := fun x => (p.toFun x.1, q.toFun x.2)
  continuous := Chapter3.prod_map_scottContinuous p.continuous q.continuous
  idem := by
    intro x
    exact Prod.ext (p.idem x.1) (q.idem x.2)
  below := by
    intro x
    exact ⟨p.below x.1, q.below x.2⟩
  finite_range := by
    apply (p.finite_range.prod q.finite_range).subset
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact ⟨⟨x.1, rfl⟩, ⟨x.2, rfl⟩⟩

end FiniteProjection

/-- Directed approximating finite projections are closed under binary
products. -/
theorem directedIdempotentDeflations_product
    {D E : OrderedDomain.{u}}
    (hD : HasDirectedIdempotentDeflationsApproximatingIdentity D)
    (hE : HasDirectedIdempotentDeflationsApproximatingIdentity E) :
    HasDirectedIdempotentDeflationsApproximatingIdentity
      (OrderedDomain.prod D E) := by
  rcases hD with ⟨P, hPnonempty, hPdirected, hPsup⟩
  rcases hE with ⟨Q, hQnonempty, hQdirected, hQsup⟩
  let I := {p : IdempotentDeflation D // p ∈ P}
  let J := {q : IdempotentDeflation E // q ∈ Q}
  let R : Set (IdempotentDeflation (OrderedDomain.prod D E)) :=
    Set.range (fun pq : I × J => FiniteProjection.prod pq.1.1 pq.2.1)
  refine ⟨R, ?_, ?_, ?_⟩
  · rcases hPnonempty with ⟨p, hp⟩
    rcases hQnonempty with ⟨q, hq⟩
    exact ⟨FiniteProjection.prod p q, ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩⟩
  · intro p hp q hq
    rcases hp with ⟨⟨pi, qi⟩, rfl⟩
    rcases hq with ⟨⟨pj, qj⟩, rfl⟩
    rcases hPdirected pi.1 pi.2 pj.1 pj.2 with ⟨pk, hpk, hpik⟩
    rcases hQdirected qi.1 qi.2 qj.1 qj.2 with ⟨qk, hqk, hqik⟩
    refine ⟨FiniteProjection.prod pk qk,
      ⟨(⟨pk, hpk⟩, ⟨qk, hqk⟩), rfl⟩, ?_⟩
    intro x
    exact ⟨⟨(hpik x.1).1, (hqik x.2).1⟩,
      ⟨(hpik x.1).2, (hqik x.2).2⟩⟩
  · intro x
    constructor
    · intro y hy
      rcases hy with ⟨r, hr, rfl⟩
      rcases hr with ⟨⟨p, q⟩, rfl⟩
      exact ⟨p.1.below x.1, q.1.below x.2⟩
    · intro y hy
      constructor
      · exact (hPsup x.1).2 y.1 (by
          intro z hz
          rcases hz with ⟨p, hp, rfl⟩
          rcases hQnonempty with ⟨q, hq⟩
          exact (hy ⟨FiniteProjection.prod p q,
            ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩, rfl⟩).1)
      · exact (hQsup x.2).2 y.2 (by
          intro z hz
          rcases hz with ⟨q, hq, rfl⟩
          rcases hPnonempty with ⟨p, hp⟩
          exact (hy ⟨FiniteProjection.prod p q,
            ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩, rfl⟩).2)

/-- The product component of Theorem 4.2.8. -/
theorem bifiniteDomainClass_closedUnderProducts :
    DomainClass.ClosedUnderProducts (BifiniteDomainClass : DomainClass.{u}) := by
  intro D E hD hE
  rcases hD with ⟨hDdcpo, hDanti, hDbif⟩
  rcases hE with ⟨hEdcpo, hEanti, hEbif⟩
  let hDbot : HasBottom D := hasBottom_of_bifiniteCompactBasis D hDbif
  let hEbot : HasBottom E := hasBottom_of_bifiniteCompactBasis E hEbif
  have hDdefl : HasDirectedIdempotentDeflationsApproximatingIdentity D :=
    (theorem_4_2_6_bifinite_functional_characterizations
      D hDdcpo hDanti hDbot).1.mp hDbif
  have hEdefl : HasDirectedIdempotentDeflationsApproximatingIdentity E :=
    (theorem_4_2_6_bifinite_functional_characterizations
      E hEdcpo hEanti hEbot).1.mp hEbif
  have hProdDcpo : Chapter3.IsDcpo (D.carrier × E.carrier) :=
    Chapter3.prod_isDcpo hDdcpo hEdcpo
  have hProdAnti : ∀ x y : D.carrier × E.carrier,
      x ≤ y → y ≤ x → x = y := by
    intro x y hxy hyx
    exact Prod.ext (hDanti x.1 y.1 hxy.1 hyx.1)
      (hEanti x.2 y.2 hxy.2 hyx.2)
  rcases hDbot with ⟨botD, hbotD⟩
  rcases hEbot with ⟨botE, hbotE⟩
  let hProdBot : HasBottom (OrderedDomain.prod D E) :=
    ⟨(botD, botE), fun x => ⟨hbotD x.1, hbotE x.2⟩⟩
  exact ⟨hProdDcpo, hProdAnti,
    (theorem_4_2_6_bifinite_functional_characterizations
      (OrderedDomain.prod D E) hProdDcpo hProdAnti hProdBot).1.mpr
        (directedIdempotentDeflations_product hDdefl hEdefl)⟩

namespace FiniteProjection

/-- The finite-step operator on a function space used in the proof of Theorem
4.2.8: `h ↦ q ∘ h ∘ p`. -/
def sandwich {D E : OrderedDomain.{u}} (p : FiniteProjection D)
    (q : FiniteProjection E) (h : OrderedDomain.ContFunCarrier D E) :
    OrderedDomain.ContFunCarrier D E :=
  OrderedDomain.compContFun
    ({ toFun := q.toFun, continuous := q.continuous } :
      OrderedDomain.ContFunCarrier E E)
    (OrderedDomain.compContFun h
      ({ toFun := p.toFun, continuous := p.continuous } :
        OrderedDomain.ContFunCarrier D D))

@[simp] theorem sandwich_apply {D E : OrderedDomain.{u}}
    (p : FiniteProjection D) (q : FiniteProjection E)
    (h : OrderedDomain.ContFunCarrier D E) (x : D.carrier) :
    sandwich p q h x = q.toFun (h (p.toFun x)) := rfl

/-- The sandwich operator is Scott-continuous in its function argument. -/
theorem sandwich_scottContinuous {D E : OrderedDomain.{u}}
    (hEdcpo : Chapter3.IsDcpo E.carrier)
    (p : FiniteProjection D) (q : FiniteProjection E) :
    Chapter3.ScottContinuous (sandwich p q) := by
  constructor
  · intro f g hfg x
    exact q.continuous.1 (hfg (p.toFun x))
  · intro A s hA hs
    constructor
    · intro y hy x
      rcases hy with ⟨f, hf, rfl⟩
      exact q.continuous.1 (hs.1 hf (p.toFun x))
    · intro g hg x
      have hEvalSup : Chapter3.IsSup
          ((fun f : OrderedDomain.ContFunCarrier D E => f (p.toFun x)) '' A)
          (s (p.toFun x)) :=
        (Chapter3.ContFun.eval_scottContinuous hEdcpo (p.toFun x)).2 hA hs
      have hEvalDirected : Chapter3.DirectedSet
          ((fun f : OrderedDomain.ContFunCarrier D E => f (p.toFun x)) '' A) :=
        Chapter3.ContFun.eval_directed hA (p.toFun x)
      exact (q.continuous.2 hEvalDirected hEvalSup).2 (g x) (by
        intro z hz
        rcases hz with ⟨w, ⟨f, hf, rfl⟩, rfl⟩
        exact hg ⟨f, hf, rfl⟩ x)

/-- The sandwich operator has finite image because its outputs are determined
by a function from the finite image of `p` to the finite image of `q`. -/
theorem sandwich_finite_range {D E : OrderedDomain.{u}}
    (p : FiniteProjection D) (q : FiniteProjection E) :
    (Set.range (sandwich p q)).Finite := by
  classical
  let Kp := finiteProjectionKernel D p
  let Kq := finiteProjectionKernel E q
  let encode : OrderedDomain.ContFunCarrier D E →
      (Kp.ImageCarrier → Kq.ImageCarrier) := fun h a => Kq.projection (h a.1)
  letI : Fintype Kp.ImageCarrier := p.finite_range.fintype
  letI : Fintype Kq.ImageCarrier := q.finite_range.fintype
  apply Set.Finite.of_finite_image (f := encode)
  · exact Set.toFinite _
  · intro f hf g hg hfg
    apply Chapter3.ContFun.ext_apply
    intro x
    have hFixed (h : OrderedDomain.ContFunCarrier D E)
        (hh : h ∈ Set.range (sandwich p q)) :
        q.toFun (h (p.toFun x)) = h x := by
      rcases hh with ⟨h0, rfl⟩
      simp only [sandwich_apply, p.idem, q.idem]
    let px : Kp.ImageCarrier := ⟨p.toFun x, ⟨x, rfl⟩⟩
    calc
      f x = (encode f px).1 := (hFixed f hf).symm
      _ = (encode g px).1 := congrArg Subtype.val (congrFun hfg px)
      _ = g x := hFixed g hg

/-- The sandwich operator is a finite projection on the function space. -/
def functionSpace {D E : OrderedDomain.{u}}
    (hEdcpo : Chapter3.IsDcpo E.carrier)
    (p : FiniteProjection D) (q : FiniteProjection E) :
    FiniteProjection (OrderedDomain.functionSpace D E) where
  toFun := sandwich p q
  continuous := sandwich_scottContinuous hEdcpo p q
  idem := by
    intro h
    apply Chapter3.ContFun.ext_apply
    intro x
    simp only [sandwich_apply, p.idem, q.idem]
  below := by
    change ∀ h : OrderedDomain.ContFunCarrier D E,
      ∀ x : D.carrier, sandwich p q h x ≤ h x
    intro h x
    exact le_trans (q.below (h (p.toFun x)))
      (h.continuous.1 (p.below x))
  finite_range := sandwich_finite_range p q

end FiniteProjection

/-- The directed family `h ↦ q ∘ h ∘ p` has pointwise supremum the identity
on the continuous function space. -/
theorem directedIdempotentDeflations_functionSpace
    {D E : OrderedDomain.{u}}
    (hEdcpo : Chapter3.IsDcpo E.carrier)
    (hD : HasDirectedIdempotentDeflationsApproximatingIdentity D)
    (hE : HasDirectedIdempotentDeflationsApproximatingIdentity E) :
    HasDirectedIdempotentDeflationsApproximatingIdentity
      (OrderedDomain.functionSpace D E) := by
  rcases hD with ⟨P, hPnonempty, hPdirected, hPsup⟩
  rcases hE with ⟨Q, hQnonempty, hQdirected, hQsup⟩
  let I := {p : IdempotentDeflation D // p ∈ P}
  let J := {q : IdempotentDeflation E // q ∈ Q}
  let R : Set (IdempotentDeflation (OrderedDomain.functionSpace D E)) :=
    Set.range (fun pq : I × J =>
      FiniteProjection.functionSpace hEdcpo pq.1.1 pq.2.1)
  refine ⟨R, ?_, ?_, ?_⟩
  · rcases hPnonempty with ⟨p, hp⟩
    rcases hQnonempty with ⟨q, hq⟩
    exact ⟨FiniteProjection.functionSpace hEdcpo p q,
      ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩⟩
  · intro p hp q hq
    rcases hp with ⟨⟨pi, qi⟩, rfl⟩
    rcases hq with ⟨⟨pj, qj⟩, rfl⟩
    rcases hPdirected pi.1 pi.2 pj.1 pj.2 with ⟨pk, hpk, hpik⟩
    rcases hQdirected qi.1 qi.2 qj.1 qj.2 with ⟨qk, hqk, hqik⟩
    refine ⟨FiniteProjection.functionSpace hEdcpo pk qk,
      ⟨(⟨pk, hpk⟩, ⟨qk, hqk⟩), rfl⟩, ?_⟩
    intro h
    change OrderedDomain.ContFunCarrier D E at h
    constructor
    · intro x
      exact (hqik (h (pi.1.toFun x))).1.trans
        (qk.continuous.1 (h.continuous.1 ((hpik x).1)))
    · intro x
      exact (hqik (h (pj.1.toFun x))).2.trans
        (qk.continuous.1 (h.continuous.1 ((hpik x).2)))
  · intro h
    change OrderedDomain.ContFunCarrier D E at h
    constructor
    · intro f hf
      rcases hf with ⟨r, hr, rfl⟩
      rcases hr with ⟨⟨p, q⟩, rfl⟩
      exact (FiniteProjection.functionSpace hEdcpo p.1 q.1).below h
    · intro g hg
      change OrderedDomain.ContFunCarrier D E at g
      intro x
      let AP : Set D.carrier := {z | ∃ p ∈ P, z = p.toFun x}
      have hAPdir : Chapter3.DirectedSet AP := by
        constructor
        · rcases hPnonempty with ⟨p, hp⟩
          exact ⟨p.toFun x, ⟨p, hp, rfl⟩⟩
        · intro a ha b hb
          rcases ha with ⟨p, hp, rfl⟩
          rcases hb with ⟨q, hq, rfl⟩
          rcases hPdirected p hp q hq with ⟨r, hr, hprq⟩
          exact ⟨r.toFun x, ⟨r, hr, rfl⟩, (hprq x).1, (hprq x).2⟩
      have hImageSup : Chapter3.IsSup (h '' AP) (h x) :=
        h.continuous.2 hAPdir (hPsup x)
      exact hImageSup.2 (g x) (by
        intro z hz
        rcases hz with ⟨px, ⟨p, hp, rfl⟩, rfl⟩
        exact (hQsup (h (p.toFun x))).2 (g x) (by
          intro w hw
          rcases hw with ⟨q, hq, rfl⟩
          exact hg ⟨FiniteProjection.functionSpace hEdcpo p q,
            ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩, rfl⟩ x))

/-- The function-space component of Theorem 4.2.8. -/
theorem bifiniteDomainClass_closedUnderFunctionSpaces :
    DomainClass.ClosedUnderFunctionSpaces
      (BifiniteDomainClass : DomainClass.{u}) := by
  intro D E hD hE
  rcases hD with ⟨hDdcpo, hDanti, hDbif⟩
  rcases hE with ⟨hEdcpo, hEanti, hEbif⟩
  let hDbot : HasBottom D := hasBottom_of_bifiniteCompactBasis D hDbif
  let hEbot : HasBottom E := hasBottom_of_bifiniteCompactBasis E hEbif
  have hDdefl : HasDirectedIdempotentDeflationsApproximatingIdentity D :=
    (theorem_4_2_6_bifinite_functional_characterizations
      D hDdcpo hDanti hDbot).1.mp hDbif
  have hEdefl : HasDirectedIdempotentDeflationsApproximatingIdentity E :=
    (theorem_4_2_6_bifinite_functional_characterizations
      E hEdcpo hEanti hEbot).1.mp hEbif
  have hFunDcpo : Chapter3.IsDcpo (OrderedDomain.ContFunCarrier D E) :=
    Chapter3.ContFun.isDcpo_of_codomain hEdcpo
  have hFunAnti : ∀ f g : OrderedDomain.ContFunCarrier D E,
      f ≤ g → g ≤ f → f = g := by
    intro f g hfg hgf
    apply Chapter3.ContFun.ext_apply
    intro x
    exact hEanti (f x) (g x) (hfg x) (hgf x)
  rcases hEbot with ⟨botE, hbotE⟩
  let botFun : OrderedDomain.ContFunCarrier D E :=
    { toFun := fun _ => botE
      continuous := Chapter3.const_scottContinuous botE }
  let hFunBot : HasBottom (OrderedDomain.functionSpace D E) :=
    ⟨botFun, by
      intro f
      change OrderedDomain.ContFunCarrier D E at f
      intro x
      exact hbotE (f x)⟩
  exact ⟨hFunDcpo, hFunAnti,
    (theorem_4_2_6_bifinite_functional_characterizations
      (OrderedDomain.functionSpace D E) hFunDcpo hFunAnti hFunBot).1.mpr
        (directedIdempotentDeflations_functionSpace hEdcpo hDdefl hEdefl)⟩

/-- Theorem 4.2.8, PDF text: bifinite domains are closed under cartesian
product, function space, coalesced sum, and bilimits; in particular `B` is
cartesian closed.  The PDF gives the idempotent-deflation proof for function
spaces, which is formalized above.  It supplies no details for the stated
elementary coalesced-sum clause and explicitly leaves bilimit closure as an
exercise, so those two components retain book-omission boundaries. -/
theorem theorem_4_2_8_bifinite_closure_properties :
    DomainClass.ClosedUnderProducts (BifiniteDomainClass : DomainClass.{u}) ∧
      DomainClass.ClosedUnderFunctionSpaces (BifiniteDomainClass : DomainClass.{u}) ∧
      DomainClass.ClosedUnderCoalescedSums (BifiniteDomainClass : DomainClass.{u}) ∧
      DomainClass.ClosedUnderExpandingBilimits (BifiniteDomainClass : DomainClass.{u}) ∧
      DomainClass.CartesianClosed (BifiniteDomainClass : DomainClass.{u}) := by
  have hProducts :
      DomainClass.ClosedUnderProducts (BifiniteDomainClass : DomainClass.{u}) := by
    exact bifiniteDomainClass_closedUnderProducts
  have hFunctionSpaces :
      DomainClass.ClosedUnderFunctionSpaces (BifiniteDomainClass : DomainClass.{u}) := by
    exact bifiniteDomainClass_closedUnderFunctionSpaces
  have hCoalescedSums :
      DomainClass.ClosedUnderCoalescedSums (BifiniteDomainClass : DomainClass.{u}) := by
    admit
  have hBilimits :
      DomainClass.ClosedUnderExpandingBilimits (BifiniteDomainClass : DomainClass.{u}) := by
    admit
  exact ⟨hProducts, hFunctionSpaces, hCoalescedSums, hBilimits,
    ⟨hProducts, hFunctionSpaces⟩⟩

/-- Definition 4.2.9 package. PDF text: an FS-domain is a pointed dcpo with a
directed collection of continuous self-maps, each finitely separated from the
identity, whose supremum is the identity map. -/
def IsFSObject (D : OrderedDomain.{u}) : Prop :=
  ∃ F : FSDomain.{u}, F.object = D

/-- Definition 4.2.9: the local predicate for FS-domains, including the
pointed-dcpo data stored in `FSDomain`. -/
def def_4_2_9_fs_domain (D : OrderedDomain.{u}) : Prop :=
  IsFSObject D

/-- Definition 4.2.9 consequence: every FS object is a dcpo. -/
theorem fsObject_isDcpo {D : OrderedDomain.{u}} (hD : IsFSObject D) :
    Chapter3.IsDcpo D.carrier := by
  rcases hD with ⟨F, rfl⟩
  exact F.dcpo

/-- Definition 4.2.9 consequence: every FS object has a least element. -/
theorem fsObject_hasBottom {D : OrderedDomain.{u}} (hD : IsFSObject D) :
    HasBottom D := by
  rcases hD with ⟨F, rfl⟩
  rcases F.pointed with ⟨bot, hbot⟩
  exact ⟨bot, hbot⟩

/-- A finitely separated continuous self-map approximates the identity in the
way-below relation.  The finite separator set turns an arbitrary directed test
set into one active separator lying below a member of that test set. -/
theorem finitelySeparatedSelfMap_wayBelow
    {D : OrderedDomain.{u}} (f : FinitelySeparatedSelfMap D)
    (x : D.carrier) : f.toFun x ≪ x := by
  classical
  intro A s hA hs hxs
  let active : Set D.carrier :=
    {m | m ∈ f.separators ∧ ∃ a ∈ A, f.toFun a ≤ m ∧ m ≤ a}
  have hActiveFinite : active.Finite := by
    exact f.finite_separators.subset (by
      intro m hm
      exact hm.1)
  have hImageDirected : Chapter3.DirectedSet (f.toFun '' A) :=
    Chapter2.DirectedSet.image f.continuous.1 hA
  have hActiveUpper :
      ∃ m ∈ active, Chapter3.IsUpperBound (f.toFun '' A) m := by
    by_contra hnone
    push Not at hnone
    have hChoose : ∀ m : active,
        ∃ y ∈ f.toFun '' A, ¬ y ≤ m.1 := by
      intro m
      have hnot := hnone m.1 m.2
      change ¬ ∀ y, y ∈ f.toFun '' A → y ≤ m.1 at hnot
      push Not at hnot
      exact hnot
    let witness : active → D.carrier := fun m => Classical.choose (hChoose m)
    letI : Finite active := Set.finite_coe_iff.mp hActiveFinite
    have hWitnessMem : ∀ m : active, witness m ∈ f.toFun '' A := by
      intro m
      exact (Classical.choose_spec (hChoose m)).1
    have hWitnessNotLe : ∀ m : active, ¬ witness m ≤ m.1 := by
      intro m
      exact (Classical.choose_spec (hChoose m)).2
    have hWitnessFinite : (Set.range witness).Finite := Set.finite_range witness
    have hWitnessSub : Set.range witness ⊆ f.toFun '' A := by
      intro y hy
      rcases hy with ⟨m, rfl⟩
      exact hWitnessMem m
    rcases hImageDirected.exists_upper_finite hWitnessFinite hWitnessSub with
      ⟨y, hyImage, hyUpper⟩
    rcases hyImage with ⟨a, haA, rfl⟩
    rcases f.separated a with ⟨m, hmSep, hfam, hma⟩
    have hmActive : m ∈ active := ⟨hmSep, a, haA, hfam, hma⟩
    have hWitnessLe : witness ⟨m, hmActive⟩ ≤ f.toFun a := by
      apply hyUpper
      exact ⟨⟨m, hmActive⟩, rfl⟩
    exact hWitnessNotLe ⟨m, hmActive⟩ (le_trans hWitnessLe hfam)
  rcases hActiveUpper with ⟨m, hmActive, hmUpper⟩
  rcases hmActive.2 with ⟨a, haA, -, hma⟩
  have hImageSup : Chapter3.IsSup (f.toFun '' A) (f.toFun s) :=
    f.continuous.2 hA hs
  have hfxs : f.toFun x ≤ f.toFun s := f.continuous.1 hxs
  exact ⟨a, haA, le_trans hfxs (le_trans (hImageSup.2 m hmUpper) hma)⟩

/-- The finite-separation presentation in Definition 4.2.9 already implies
continuity of the underlying dcpo; no use of the conjectural Proposition 4.2.10
is needed. -/
theorem fsObject_isContinuousDomain {D : OrderedDomain.{u}} (hD : IsFSObject D) :
    Chapter3.IsContinuousDomain D.carrier := by
  rcases hD with ⟨F, rfl⟩
  have hRaw : Chapter2.IsBasisRaw (Set.univ : Set F.object.carrier) := by
    intro x
    let A : Set F.object.carrier :=
      {y | ∃ f ∈ F.maps, y = f.toFun x}
    refine ⟨A, ?_, ?_, F.approximates x⟩
    · intro y hy
      rcases hy with ⟨f, hf, rfl⟩
      exact ⟨Set.mem_univ _, finitelySeparatedSelfMap_wayBelow f x⟩
    · constructor
      · rcases F.nonempty with ⟨f, hf⟩
        exact ⟨f.toFun x, f, hf, rfl⟩
      · intro y hy z hz
        rcases hy with ⟨f, hf, rfl⟩
        rcases hz with ⟨g, hg, rfl⟩
        rcases F.directed f hf g hg with ⟨h, hh, hfg⟩
        exact ⟨h.toFun x, ⟨h, hh, rfl⟩, (hfg x).1, (hfg x).2⟩
  exact ⟨Set.univ, Chapter2.prop_2_2_4_1 hRaw⟩

/-- The Chapter 4 class of FS-domains. -/
def FSDomainClass : DomainClass.{u} where
  Obj := IsFSObject

/-- Proposition 4.2.10 as printed in the PDF.  The immediately following source
comment says its proof was unknown.  Therefore Lean records only the conjectural
statement and deliberately provides no proof constant. -/
def conjecture_4_2_10_fs_function_space : Prop :=
  ∀ {D E : OrderedDomain.{u}}, IsFSObject D → IsPointedContinuousDomain E →
    Chapter3.IsContinuousDomain (OrderedDomain.functionSpace D E).carrier

/-- Compatibility name preserving the textbook's source number.  This is a
proposition-valued definition, not a theorem and not evidence for the claim. -/
abbrev prop_4_2_10_fs_function_space : Prop :=
  conjecture_4_2_10_fs_function_space.{u}

/-- External result used by Theorem 4.2.11.  Jung [Jun90, Theorem 2.2.6]
states that arbitrary products and inverse limits of FS-domains are FS-domains
and proves explicitly that the continuous-function space of two FS-domains is
again an FS-domain.  The three fields below are the binary-product,
function-space, and expanding-sequence specializations of that result.

Reference: A. Jung, *The classification of continuous domains*, LICS 1990,
Theorem 2.2.6 (pp. 48--49 in the reprint). -/
axiom jun90_theorem_2_2_6_fs_closure :
    DomainClass.ClosedUnderProducts (FSDomainClass : DomainClass.{u}) ∧
      DomainClass.ClosedUnderFunctionSpaces (FSDomainClass : DomainClass.{u}) ∧
        DomainClass.ClosedUnderExpandingBilimits (FSDomainClass : DomainClass.{u})

/-- Theorem 4.2.11, PDF text: `FS` is closed under products, function spaces,
coalesced sums, and bilimits, hence cartesian closed.  Jung [Jun90,
Theorem 2.2.6] supplies the product, function-space, and inverse-limit clauses.
The book gives no proof or separate external citation for the coalesced-sum
clause, so only that component remains a book-omission boundary. -/
theorem theorem_4_2_11_fs_closure_properties :
    DomainClass.ClosedUnderProducts (FSDomainClass : DomainClass.{u}) ∧
      DomainClass.ClosedUnderFunctionSpaces (FSDomainClass : DomainClass.{u}) ∧
      DomainClass.ClosedUnderCoalescedSums (FSDomainClass : DomainClass.{u}) ∧
      DomainClass.ClosedUnderExpandingBilimits (FSDomainClass : DomainClass.{u}) ∧
      DomainClass.CartesianClosed (FSDomainClass : DomainClass.{u}) := by
  rcases jun90_theorem_2_2_6_fs_closure with
    ⟨hProducts, hFunctionSpaces, hBilimits⟩
  have hCoalescedSums :
      DomainClass.ClosedUnderCoalescedSums (FSDomainClass : DomainClass.{u}) := by
    admit
  exact ⟨hProducts, hFunctionSpaces, hCoalescedSums, hBilimits,
    ⟨hProducts, hFunctionSpaces⟩⟩

/-- A continuous retract relation between ordered domains: `D` is a continuous
retract of `E` when there is a continuous section-retraction pair from `D` into
`E`. -/
def IsContinuousRetractOf (D E : OrderedDomain.{u}) : Prop :=
  Nonempty (Chapter3.ContinuousSectionRetractionPair D.carrier E.carrier)

/-- Proposition 4.2.12(1): compact-basis bifinite domains are FS-domains. -/
def BifiniteImpliesFS : Prop :=
  ∀ D : OrderedDomain.{u}, HasBifiniteCompactBasis D → IsFSObject D

/-- Proposition 4.2.12(2): continuous retracts of FS-domains are FS-domains. -/
def FSClosedUnderContinuousRetracts : Prop :=
  ∀ D E : OrderedDomain.{u}, IsContinuousRetractOf D E → IsFSObject E → IsFSObject D

/-- Proposition 4.2.12(3): algebraic FS-domains are compact-basis bifinite. -/
def AlgebraicFSImpliesBifinite : Prop :=
  ∀ D : OrderedDomain.{u}, Chapter3.IsAlgebraicDomain D.carrier →
    IsFSObject D → HasBifiniteCompactBasis D

/-- Proposition 4.2.12 statement package: the three FS/bifinite/retract
relationships listed in the PDF. -/
def BifiniteFSRelationships : Prop :=
  BifiniteImpliesFS.{u} ∧ FSClosedUnderContinuousRetracts.{u} ∧
    AlgebraicFSImpliesBifinite.{u}

/-- Proposition 4.2.12, PDF text: bifinite domains are FS; continuous retracts
of FS-domains are FS; and algebraic FS-domains are bifinite.  The proof is not
formalized here, so the package is registered as local proof debt. -/
theorem prop_4_2_12_bifinite_fs_relationships :
    BifiniteFSRelationships.{u} := by
  admit

/-- Proposition 4.2.12(1). -/
theorem prop_4_2_12_bifinite_implies_fs
    (D : OrderedDomain.{u}) (hD : HasBifiniteCompactBasis D) :
    IsFSObject D := by
  exact prop_4_2_12_bifinite_fs_relationships.1 D hD

/-- Proposition 4.2.12(2). -/
theorem prop_4_2_12_fs_closed_under_retracts
    (D E : OrderedDomain.{u}) (hRetract : IsContinuousRetractOf D E)
    (hE : IsFSObject E) :
    IsFSObject D := by
  exact prop_4_2_12_bifinite_fs_relationships.2.1 D E hRetract hE

/-- Proposition 4.2.12(3). -/
theorem prop_4_2_12_algebraic_fs_bifinite
    (D : OrderedDomain.{u}) (hAlg : Chapter3.IsAlgebraicDomain D.carrier)
    (hFS : IsFSObject D) :
    HasBifiniteCompactBasis D := by
  exact prop_4_2_12_bifinite_fs_relationships.2.2 D hAlg hFS

/-- A Scott-compact subset, expressed through Scott-open covers. -/
def IsScottCompactSet (D : OrderedDomain.{u}) (A : Set D.carrier) : Prop :=
  ∀ cover : Set (Set D.carrier),
    (∀ U ∈ cover, Chapter2.ScottOpen U) →
      A ⊆ ⋃₀ cover →
        ∃ finiteCover : Set (Set D.carrier),
          finiteCover ⊆ cover ∧ finiteCover.Finite ∧ A ⊆ ⋃₀ finiteCover

/-- Saturated sets for the Scott topology, represented order-theoretically as upper sets. -/
def IsSaturatedSet (D : OrderedDomain.{u}) (A : Set D.carrier) : Prop :=
  ∀ ⦃x y : D.carrier⦄, x ∈ A → x ≤ y → y ∈ A

/-- Compact saturated subsets of a dcpo. -/
def IsCompactSaturated (D : OrderedDomain.{u}) (A : Set D.carrier) : Prop :=
  IsScottCompactSet D A ∧ IsSaturatedSet D A

/-- Compact saturated subsets as an ordered carrier.  The order is reverse
inclusion, as in the Smyth/upper powerdomain presentation. -/
structure CompactSaturatedCarrier (D : OrderedDomain.{u}) where
  carrierSet : Set D.carrier
  compact_saturated : IsCompactSaturated D carrierSet

instance compactSaturatedCarrierPreorder (D : OrderedDomain.{u}) :
    Preorder (CompactSaturatedCarrier D) where
  le A B := B.carrierSet ⊆ A.carrierSet
  le_refl A := by intro x hx; exact hx
  le_trans A B C hAB hBC := by
    intro x hx
    exact hAB (hBC hx)

/-- The nonempty part `κD \ {∅}` from Proposition 4.2.14. -/
structure NonemptyCompactSaturatedCarrier (D : OrderedDomain.{u}) where
  carrierSet : Set D.carrier
  compact_saturated : IsCompactSaturated D carrierSet
  nonempty : carrierSet.Nonempty

instance nonemptyCompactSaturatedCarrierPreorder (D : OrderedDomain.{u}) :
    Preorder (NonemptyCompactSaturatedCarrier D) where
  le A B := B.carrierSet ⊆ A.carrierSet
  le_refl A := by intro x hx; exact hx
  le_trans A B C hAB hBC := by
    intro x hx
    exact hAB (hBC hx)

/-- Scott opens as an ordered carrier, ordered by inclusion. -/
structure ScottOpenCarrier (D : OrderedDomain.{u}) where
  carrierSet : Set D.carrier
  scott_open : Chapter2.ScottOpen carrierSet

instance scottOpenCarrierPreorder (D : OrderedDomain.{u}) :
    Preorder (ScottOpenCarrier D) where
  le O U := O.carrierSet ⊆ U.carrierSet
  le_refl O := by intro x hx; exact hx
  le_trans O U V hOU hUV := by
    intro x hx
    exact hUV (hOU hx)

namespace ScottOpenCarrier

/-- Binary intersection in the Scott-open carrier `σD`. -/
def inter (D : OrderedDomain.{u}) (O U : ScottOpenCarrier D) : ScottOpenCarrier D where
  carrierSet := O.carrierSet ∩ U.carrierSet
  scott_open := Chapter2.scottOpen_inter O.scott_open U.scott_open

end ScottOpenCarrier

/-- Open neighborhoods of a subset in the Scott topology. -/
def ScottNeighborhoods (D : OrderedDomain.{u}) (A : Set D.carrier) : Set (Set D.carrier) :=
  {U | Chapter2.ScottOpen U ∧ A ⊆ U}

/-- Scott-open filters in the lattice `σD` of Scott opens.  Besides being a
filter of Scott-open subsets, the corresponding subset of `σD` is Scott-open in
the inclusion order on Scott opens. -/
def IsScottOpenFilter (D : OrderedDomain.{u}) (F : Set (Set D.carrier)) : Prop :=
  F.Nonempty ∧
    (∀ U ∈ F, Chapter2.ScottOpen U) ∧
      Chapter2.ScottOpen ({U : ScottOpenCarrier D | U.carrierSet ∈ F}) ∧
        (∀ U V, U ∈ F → U ⊆ V → Chapter2.ScottOpen V → V ∈ F) ∧
          ∀ U V, U ∈ F → V ∈ F → U ∩ V ∈ F

end Chapter4
end AbramskyJung

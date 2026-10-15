import Practice.DomainTheory.Chapter02.Section21

set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-!
# Abramsky--Jung, Domain Theory, Chapter 2: Section 2.2: approximation

Book-facing declarations are kept in source order. Reusable order-theoretic
interfaces remain in `Practice.DomainTheory.Order` and
`Practice.DomainTheory.Topology`.
-/

universe u v w

namespace AbramskyJung
namespace Chapter2

section NumberedCoverageApproximation

variable {α : Type u} [Preorder α]

/-- Definition 2.2.8: inductive closure systems are closed under directed unions. -/
def ClosureSystem.IsInductive (C : ClosureSystem α) : Prop :=
  ∀ F : Set (Set α), DirectedSet F → F ⊆ C.closed → ⋃₀ F ∈ C.closed

/-- Proposition 2.2.9: finitely generated hulls in a closure system. -/
def ClosureSystem.IsFinitelyGeneratedHull
    (C : ClosureSystem α) (A : Set α) : Prop :=
  ∃ M : Set α, M.Finite ∧ A = C.closure M

omit [Preorder α] in
/-- Proposition 2.2.9: every inductive closure system is an algebraic lattice. -/
theorem prop_2_2_9_inductive_closure_system_algebraic
    (C : ClosureSystem α) (hC : C.IsInductive) :
    IsAlgebraicDomain {A : Set α // A ∈ C.closed} := by
  classical
  let Closed : Type u := {A : Set α // A ∈ C.closed}
  have hFiniteHullCompact :
      ∀ {M : Set α}, M.Finite →
        Compact (⟨C.closure M, C.closure_mem M⟩ : Closed) := by
    intro M hM D S hD hSup hMS
    let imageFamily : Set (Set α) := (fun X : Closed => X.1) '' D
    have hImageDirected : DirectedSet imageFamily := by
      constructor
      · rcases hD.1 with ⟨d, hd⟩
        exact ⟨d.1, ⟨d, hd, rfl⟩⟩
      · intro U hU V hV
        rcases hU with ⟨U', hU'D, rfl⟩
        rcases hV with ⟨V', hV'D, rfl⟩
        rcases hD.2 hU'D hV'D with ⟨W, hWD, hUW, hVW⟩
        exact ⟨W.1, ⟨W, hWD, rfl⟩, hUW, hVW⟩
    have hImageClosed : imageFamily ⊆ C.closed := by
      intro U hU
      rcases hU with ⟨U', _hU'D, rfl⟩
      exact U'.2
    let Uset : Set α := ⋃₀ imageFamily
    have hUclosed : Uset ∈ C.closed := hC imageFamily hImageDirected hImageClosed
    let U : Closed := ⟨Uset, hUclosed⟩
    have hUsup : IsSup D U := by
      constructor
      · intro d hd x hx
        exact ⟨d.1, ⟨d, hd, rfl⟩, hx⟩
      · intro Z hZ x hx
        rcases hx with ⟨T, hT, hxT⟩
        rcases hT with ⟨d, hd, rfl⟩
        exact hZ hd hxT
    have hSU : S = U := IsSup.unique hSup hUsup
    have hPointWitness : ∀ x ∈ M, ∃ d ∈ D, x ∈ d.1 := by
      intro x hxM
      have hxS : x ∈ S.1 := hMS (C.subset_closure (A := M) hxM)
      have hxU : x ∈ U.1 := by
        simpa [hSU] using hxS
      rcases hxU with ⟨T, hT, hxT⟩
      rcases hT with ⟨d, hd, rfl⟩
      exact ⟨d, hd, hxT⟩
    rcases hD.1 with ⟨default, hdefault⟩
    let pick : α → Closed := fun x =>
      if hx : x ∈ M then Classical.choose (hPointWitness x hx) else default
    have hpick_mem : ∀ x ∈ M, pick x ∈ D := by
      intro x hx
      dsimp [pick]
      simp [hx, (Classical.choose_spec (hPointWitness x hx)).1]
    have hpick_contains : ∀ x ∈ M, x ∈ (pick x).1 := by
      intro x hx
      dsimp [pick]
      simp [hx, (Classical.choose_spec (hPointWitness x hx)).2]
    let F : Set Closed := pick '' M
    have hFfin : F.Finite := hM.image pick
    have hFsub : F ⊆ D := by
      intro d hd
      rcases hd with ⟨x, hxM, rfl⟩
      exact hpick_mem x hxM
    rcases DirectedSet.exists_upper_finite hD hFfin hFsub with ⟨d, hdD, hdUpper⟩
    refine ⟨d, hdD, ?_⟩
    exact C.closure_least d.2 (by
      intro x hxM
      exact hdUpper (pick x) ⟨x, hxM, rfl⟩ (hpick_contains x hxM))
  intro X
  let finiteHulls : Set Closed :=
    {Y | ∃ M : Set α, M.Finite ∧ M ⊆ X.1 ∧
      Y = ⟨C.closure M, C.closure_mem M⟩}
  refine ⟨finiteHulls, ?_, ?_, ?_⟩
  · intro Y hY
    rcases hY with ⟨M, hMfin, hMX, rfl⟩
    have hCompact :
        Compact (⟨C.closure M, C.closure_mem M⟩ : Closed) :=
      hFiniteHullCompact hMfin
    have hBelowX : (⟨C.closure M, C.closure_mem M⟩ : Closed) ≤ X :=
      C.closure_least X.2 hMX
    exact ⟨hCompact, prop_2_2_2_2 le_rfl hCompact hBelowX⟩
  · constructor
    · refine ⟨(⟨C.closure ∅, C.closure_mem ∅⟩ : Closed), ?_⟩
      exact ⟨∅, Set.finite_empty, ⟨(by intro x hx; cases hx), rfl⟩⟩
    · intro Y hY Z hZ
      rcases hY with ⟨M, hMfin, hMX, rfl⟩
      rcases hZ with ⟨N, hNfin, hNX, rfl⟩
      refine ⟨(⟨C.closure (M ∪ N), C.closure_mem (M ∪ N)⟩ : Closed), ?_, ?_, ?_⟩
      · exact ⟨M ∪ N, hMfin.union hNfin, ⟨(by
          intro x hx
          rcases hx with hxM | hxN
          · exact hMX hxM
          · exact hNX hxN), rfl⟩⟩
      · exact C.closure_least (C.closure_mem (M ∪ N)) (by
          intro x hx
          exact C.subset_closure (A := M ∪ N) (Or.inl hx))
      · exact C.closure_least (C.closure_mem (M ∪ N)) (by
          intro x hx
          exact C.subset_closure (A := M ∪ N) (Or.inr hx))
  · constructor
    · intro Y hY
      rcases hY with ⟨M, _hMfin, hMX, rfl⟩
      exact C.closure_least X.2 hMX
    · intro Z hZ x hxX
      have hSingleton : (⟨C.closure ({x} : Set α),
          C.closure_mem ({x} : Set α)⟩ : Closed) ∈ finiteHulls := by
        refine ⟨({x} : Set α), Set.finite_singleton x, ⟨?_, rfl⟩⟩
        intro y hy
        have hyx : y = x := by simpa using hy
        simpa [hyx] using hxX
      exact hZ hSingleton (C.subset_closure (A := ({x} : Set α)) (by simp))

/-- Proposition 2.2.11: basis criterion for Scott-continuity. -/
theorem prop_2_2_11_basis_continuity_criterion
    {β : Type v} [Preorder β] {B : Set α} {C : Set β} {f : α → β}
    (hB : IsBasis B) (hC : IsBasis C) :
    ScottContinuous f ↔
      ∀ x : α, ∀ e : β, e ∈ Approximants C (f x) →
        ∃ d ∈ Approximants B x, ∀ y : α, d ≤ y → e ≤ f y := by
  constructor
  · intro hf x e he
    have hdir : DirectedSet (Approximants B x) := (hB x).1
    have hsup : IsSup (Approximants B x) x := (hB x).2
    have hfsup : IsSup (f '' Approximants B x) (f x) := hf.2 hdir hsup
    rcases he.2 (DirectedSet.image hf.1 hdir) hfsup le_rfl with
      ⟨fx', hfx', hef⟩
    rcases hfx' with ⟨d, hd, rfl⟩
    refine ⟨d, hd, ?_⟩
    intro y hdy
    exact le_trans hef (hf.1 hdy)
  · intro hcrit
    have hmono : Monotone f := by
      intro x y hxy
      exact (hC (f x)).2.2 (f y) (by
        intro e he
        rcases hcrit x e he with ⟨d, hd, hde⟩
        exact hde y (le_trans (prop_2_2_2_1 hd.2) hxy))
    constructor
    · exact hmono
    · intro A x hA hx
      constructor
      · intro z hz
        rcases hz with ⟨a, ha, rfl⟩
        exact hmono (hx.1 ha)
      · intro y hy
        exact (hC (f x)).2.2 y (by
          intro e he
          rcases hcrit x e he with ⟨d, hd, hde⟩
          rcases hd.2 hA hx le_rfl with ⟨a, ha, hda⟩
          exact le_trans (hde a hda) (hy ⟨a, ha, rfl⟩))

omit [Preorder α] in
/-- Proposition 2.2.12 target record: an ω-chain of basis elements computing
the Kleene fixed point, including the book's `b_{n+1} ≤ f(b_n)` condition and
the equality with the supremum of finite Kleene iterates. -/
structure OmegaBasisFixpointChain
    [PartialOrder α] [OrderBot α] (B : Set α) (f : ScottContFun α α) where
  b : Nat → α
  kleene : Nat → α
  fixpoint : α
  mem_basis : ∀ n : Nat, b n ∈ B
  bottom_eq : b 0 = ⊥
  monotone : Monotone b
  step_le : ∀ n : Nat, b (n + 1) ≤ f (b n)
  kleene_zero : kleene 0 = ⊥
  kleene_succ : ∀ n : Nat, kleene (n + 1) = f (kleene n)
  fixpoint_isLeast : IsLeastFixedPoint f fixpoint
  chain_sup_fix : IsSup (Set.range b) fixpoint
  kleene_sup_fix : IsSup (Set.range kleene) fixpoint

/-- Proposition 2.2.12, full cited form (Abramsky [Abr90b]): in a pointed
ω-continuous dcpo with a chosen countable basis, a Scott-continuous endomap has
a basis-element ω-chain computing its least fixed point.  The dcpo hypothesis is
explicit because this file's local `IsOmegaContinuousDomain` predicate records
the countable-basis part separately.  The book cites the proof to [Abr90b], so
this full-strength statement is imported as a documented external assumption; the
following theorem is the weaker directly proved clause currently available in
this file. -/
axiom prop_2_2_12_omega_basis_fixpoint_chain_full
    [PartialOrder α] [OrderBot α] {B : Set α}
    (hD : IsDcpo α) (hBcount : B.Countable) (hB : IsBasisRaw B)
    (f : ScottContFun α α) :
    Nonempty (OmegaBasisFixpointChain B f)

/-- Proposition 2.2.12 weak clause: a continuous endomap on a pointed
ω-continuous domain has a countable-basis chain satisfying one-step lower bounds. -/
theorem prop_2_2_12_omega_basis_fixpoint_chain
    [OrderBot α] (hanti : ∀ ⦃x y : α⦄, x ≤ y → y ≤ x → x = y)
    (hD : IsOmegaContinuousDomain α) {f : α → α}
    (hf : ScottContinuous f) :
    ∃ B : Set α, B.Countable ∧ IsBasisRaw B ∧
      ∃ b : Nat → α,
        (∀ n : Nat, b n ∈ B) ∧
        b 0 = ⊥ ∧
        Monotone b ∧
        (∀ n : Nat, b (n + 1) ≤ f (b n)) := by
  have _hfmono : Monotone f := hf.1
  rcases hD with ⟨B, hBcount, hBraw⟩
  rcases hBraw (⊥ : α) with ⟨A, hAsub, hAdir, hAsup⟩
  rcases hAdir.1 with ⟨a, haA⟩
  have haB : a ∈ B := (hAsub haA).1
  have ha_bot : a ≤ (⊥ : α) := hAsup.1 haA
  have hbotB : (⊥ : α) ∈ B := by
    have h_eq : a = (⊥ : α) := hanti ha_bot bot_le
    simpa [h_eq] using haB
  refine ⟨B, hBcount, hBraw, (fun _ : Nat => (⊥ : α)), ?_, rfl, ?_, ?_⟩
  · intro n
    exact hbotB
  · intro m n hmn
    exact le_rfl
  · intro n
    exact bot_le

/-- Proposition 2.2.13: countable bases reduce directed suprema to ω-chains. -/
theorem prop_2_2_13_countable_basis_has_cofinal_omega_chain
    {B A : Set α} {s : α}
    (hBcount : B.Countable) (hB : IsBasisRaw B)
    (hA : DirectedSet A) (hs : IsSup A s) :
    ∃ c : Nat → α, Monotone c ∧ (∀ n : Nat, c n ∈ A) ∧ IsSup (Set.range c) s := by
  classical
  have hBasis : IsBasis B := prop_2_2_4_1 hB
  have hApproxDir : DirectedSet (Approximants B s) := (hBasis s).1
  have hApproxSup : IsSup (Approximants B s) s := (hBasis s).2
  rcases hApproxDir.1 with ⟨default, hdefault⟩
  have hApproxCount : (Approximants B s).Countable :=
    Set.Countable.mono (by intro x hx; exact hx.1) hBcount
  let e : Nat → α := Set.enumerateCountable hApproxCount default
  have he_mem : ∀ n : Nat, e n ∈ Approximants B s := by
    intro n
    exact Set.enumerateCountable_mem hApproxCount hdefault n
  have he_cover : Approximants B s ⊆ Set.range e := by
    intro b hb
    exact Set.subset_range_enumerate hApproxCount default hb
  have hu_exists : ∀ n : Nat, ∃ a ∈ A, e n ≤ a := by
    intro n
    exact (he_mem n).2 hA hs le_rfl
  let u : Nat → α := fun n => Classical.choose (hu_exists n)
  have hu_mem : ∀ n : Nat, u n ∈ A := by
    intro n
    exact (Classical.choose_spec (hu_exists n)).1
  have he_le_u : ∀ n : Nat, e n ≤ u n := by
    intro n
    exact (Classical.choose_spec (hu_exists n)).2
  let c : Nat → α := DirectedSet.cumulativeUpper hA u hu_mem
  refine ⟨c, ?_, ?_, ?_⟩
  · exact DirectedSet.cumulativeUpper_monotone hA u hu_mem
  · intro n
    exact DirectedSet.cumulativeUpper_mem hA u hu_mem n
  · constructor
    · intro x hx
      rcases hx with ⟨n, rfl⟩
      exact hs.1 (DirectedSet.cumulativeUpper_mem hA u hu_mem n)
    · intro y hy
      refine hApproxSup.2 y ?_
      intro b hb
      rcases he_cover hb with ⟨n, rfl⟩
      exact le_trans (he_le_u n)
        (le_trans (DirectedSet.le_cumulativeUpper_self hA u hu_mem n) (hy ⟨n, rfl⟩))

/-- Proposition 2.2.14: ω-chain completeness. -/
def IsOmegaCcpo (α : Type u) [Preorder α] : Prop :=
  ∀ c : Nat → α, Monotone c → ∃ s : α, IsSup (Set.range c) s

/-- The omega-approximation relation used in Proposition 2.2.14.  It tests
only increasing omega-chains, rather than arbitrary directed sets. -/
def OmegaWayBelow (x y : α) : Prop :=
  ∀ ⦃c : Nat → α⦄ ⦃s : α⦄,
    Monotone c → IsSup (Set.range c) s → y ≤ s → ∃ n : Nat, x ≤ c n

/-- Compactness for omega-chain approximation. -/
def OmegaCompact (x : α) : Prop :=
  OmegaWayBelow x x

/-- The set of omega-compact elements. -/
def OmegaCompactSet : Set α :=
  {x | OmegaCompact x}

/-- A basis in the sense of continuous omega-ccpos: each element is the
supremum of an increasing omega-chain of basis elements omega-approximating it. -/
def IsOmegaBasis (B : Set α) : Prop :=
  ∀ x : α, ∃ c : Nat → α,
    Monotone c ∧
      (∀ n : Nat, c n ∈ B ∧ OmegaWayBelow (c n) x) ∧
        IsSup (Set.range c) x

/-- An omega-ccpo whose underlying preorder is antisymmetric. -/
def IsOmegaCcpoOrder (α : Type u) [Preorder α] : Prop :=
  IsOmegaCcpo α ∧ IsAntisymmetricOrder α

/-- A continuous omega-ccpo in the source sense of Proposition 2.2.14. -/
def IsContinuousOmegaCcpo (α : Type u) [Preorder α] : Prop :=
  IsOmegaCcpoOrder α ∧ ∃ B : Set α, B.Countable ∧ IsOmegaBasis B

/-- An algebraic omega-ccpo in the source sense of Proposition 2.2.14. -/
def IsAlgebraicOmegaCcpo (α : Type u) [Preorder α] : Prop :=
  IsOmegaCcpoOrder α ∧
    (OmegaCompactSet : Set α).Countable ∧ IsOmegaBasis (OmegaCompactSet : Set α)

/-- The range of an increasing omega-chain is directed. -/
theorem omegaChain_directed (c : Nat → α) (hc : Monotone c) :
    DirectedSet (Set.range c) := by
  constructor
  · exact ⟨c 0, 0, rfl⟩
  · intro x hx y hy
    rcases hx with ⟨m, rfl⟩
    rcases hy with ⟨n, rfl⟩
    refine ⟨c (max m n), ⟨max m n, rfl⟩, ?_, ?_⟩
    · exact hc (Nat.le_max_left m n)
    · exact hc (Nat.le_max_right m n)

/-- Omega-approximation implies the underlying order comparison. -/
theorem omegaWayBelow_le {x y : α} (hxy : OmegaWayBelow x y) : x ≤ y := by
  let c : Nat → α := fun _ => y
  have hc : Monotone c := by
    intro m n _hmn
    exact le_rfl
  have hs : IsSup (Set.range c) y := by
    simpa [c] using isSup_singleton y
  rcases hxy hc hs le_rfl with ⟨n, hn⟩
  exact hn

/-- In a continuous omega-ccpo, every directed set has an increasing
omega-chain inside it with the same supremum. -/
theorem continuousOmegaCcpo_directed_has_cofinal_omegaChain
    (hD : IsContinuousOmegaCcpo α) {A : Set α} (hA : DirectedSet A) :
    ∃ c : Nat → α, Monotone c ∧ (∀ n : Nat, c n ∈ A) ∧
      ∃ s : α, IsSup A s ∧ IsSup (Set.range c) s := by
  classical
  rcases hD.2 with ⟨B, hBcount, hBasis⟩
  rcases hA.1 with ⟨a0, ha0⟩
  rcases hBasis a0 with ⟨d0, hd0mono, hd0basis, hd0sup⟩
  let S : Set α := {b | b ∈ B ∧ ∃ a ∈ A, OmegaWayBelow b a}
  have hScount : S.Countable :=
    Set.Countable.mono (by intro b hb; exact hb.1) hBcount
  have hdefaultS : d0 0 ∈ S :=
    ⟨(hd0basis 0).1, ⟨a0, ha0, (hd0basis 0).2⟩⟩
  let e : Nat → α := Set.enumerateCountable hScount (d0 0)
  have he_mem : ∀ n : Nat, e n ∈ S := by
    intro n
    exact Set.enumerateCountable_mem hScount hdefaultS n
  have hu_exists : ∀ n : Nat, ∃ a ∈ A, OmegaWayBelow (e n) a := by
    intro n
    exact (he_mem n).2
  let u : Nat → α := fun n => Classical.choose (hu_exists n)
  have hu_mem : ∀ n : Nat, u n ∈ A := by
    intro n
    exact (Classical.choose_spec (hu_exists n)).1
  have he_le_u : ∀ n : Nat, e n ≤ u n := by
    intro n
    exact omegaWayBelow_le (Classical.choose_spec (hu_exists n)).2
  let c : Nat → α := DirectedSet.cumulativeUpper hA u hu_mem
  have hcmono : Monotone c :=
    DirectedSet.cumulativeUpper_monotone hA u hu_mem
  rcases hD.1.1 c hcmono with ⟨s, hcsup⟩
  refine ⟨c, hcmono, DirectedSet.cumulativeUpper_mem hA u hu_mem, s, ?_, hcsup⟩
  constructor
  · intro a ha
    rcases hBasis a with ⟨d, hdmono, hdbasis, hdsup⟩
    refine hdsup.2 s ?_
    intro b hb
    rcases hb with ⟨n, rfl⟩
    have hdnS : d n ∈ S :=
      ⟨(hdbasis n).1, ⟨a, ha, (hdbasis n).2⟩⟩
    rcases Set.subset_range_enumerate hScount (d0 0) hdnS with ⟨m, hm⟩
    rw [← hm]
    exact le_trans (he_le_u m)
      (le_trans (DirectedSet.le_cumulativeUpper_self hA u hu_mem m)
        (hcsup.1 ⟨m, rfl⟩))
  · intro y hy
    exact hcsup.2 y (by
      intro x hx
      rcases hx with ⟨n, rfl⟩
      exact hy (DirectedSet.cumulativeUpper_mem hA u hu_mem n))

/-- On a continuous omega-ccpo, omega-approximation and ordinary directed
approximation coincide. -/
theorem omegaWayBelow_iff_wayBelow
    (hD : IsContinuousOmegaCcpo α) {x y : α} :
    OmegaWayBelow x y ↔ x ≪ y := by
  constructor
  · intro hxy A s hA hs hys
    rcases continuousOmegaCcpo_directed_has_cofinal_omegaChain hD hA with
      ⟨c, hcmono, hcA, t, htA, hct⟩
    have hst : s ≤ t := hs.2 t htA.1
    rcases hxy hcmono hct (le_trans hys hst) with ⟨n, hxn⟩
    exact ⟨c n, hcA n, hxn⟩
  · intro hxy c s hc hs hys
    rcases hxy (omegaChain_directed c hc) hs hys with ⟨a, ha, hxa⟩
    rcases ha with ⟨n, rfl⟩
    exact ⟨n, hxa⟩

/-- An omega-basis becomes an ordinary approximation basis once the ambient
continuous omega-ccpo supplies cofinal omega-chains for directed sets. -/
theorem isBasisRaw_of_isOmegaBasis
    (hD : IsContinuousOmegaCcpo α) {B : Set α} (hB : IsOmegaBasis B) :
    IsBasisRaw B := by
  intro x
  rcases hB x with ⟨c, hcmono, hcbasis, hcsup⟩
  refine ⟨Set.range c, ?_, omegaChain_directed c hcmono, hcsup⟩
  intro y hy
  rcases hy with ⟨n, rfl⟩
  exact ⟨(hcbasis n).1, (omegaWayBelow_iff_wayBelow hD).1 (hcbasis n).2⟩

/-- Proposition 2.2.14: ω-continuous maps preserve ω-chain suprema. -/
def OmegaContinuousMap {β : Type v} [Preorder β] (f : α → β) : Prop :=
  Monotone f ∧
    ∀ ⦃c : Nat → α⦄ ⦃s : α⦄,
      Monotone c → IsSup (Set.range c) s → IsSup (f '' Set.range c) (f s)

/-- Compatibility theorem for the older countable ordinary-way-below basis
interface.  Proposition 2.2.14 itself is stated below with `OmegaWayBelow`. -/
theorem omega_ccpo_dcpo_of_countable_wayBelow_basis
    (hω : IsOmegaCcpo α) (hcont : IsOmegaContinuousDomain α) :
    IsDcpo α := by
  classical
  rcases hcont with ⟨B, hBcount, hBraw⟩
  have hBasis : IsBasis B := prop_2_2_4_1 hBraw
  intro A hA
  let S : Set α := {b | b ∈ B ∧ ∃ a ∈ A, b ≪ a}
  have hScount : S.Countable :=
    Set.Countable.mono (by intro b hb; exact hb.1) hBcount
  rcases hA.1 with ⟨a₀, ha₀⟩
  have hApproxDir₀ : DirectedSet (Approximants B a₀) := (hBasis a₀).1
  rcases hApproxDir₀.1 with ⟨default, hdefaultApprox⟩
  have hdefaultS : default ∈ S :=
    ⟨hdefaultApprox.1, ⟨a₀, ha₀, hdefaultApprox.2⟩⟩
  let e : Nat → α := Set.enumerateCountable hScount default
  have he_mem : ∀ n : Nat, e n ∈ S := by
    intro n
    exact Set.enumerateCountable_mem hScount hdefaultS n
  have hu_exists : ∀ n : Nat, ∃ a ∈ A, e n ≪ a := by
    intro n
    exact (he_mem n).2
  let u : Nat → α := fun n => Classical.choose (hu_exists n)
  have hu_mem : ∀ n : Nat, u n ∈ A := by
    intro n
    exact (Classical.choose_spec (hu_exists n)).1
  have he_wayBelow_u : ∀ n : Nat, e n ≪ u n := by
    intro n
    exact (Classical.choose_spec (hu_exists n)).2
  let c : Nat → α := DirectedSet.cumulativeUpper hA u hu_mem
  have hc_mono : Monotone c :=
    DirectedSet.cumulativeUpper_monotone hA u hu_mem
  rcases hω c hc_mono with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  constructor
  · intro a ha
    have hApproxSup : IsSup (Approximants B a) a := (hBasis a).2
    refine hApproxSup.2 s ?_
    intro b hb
    have hbS : b ∈ S := ⟨hb.1, ⟨a, ha, hb.2⟩⟩
    rcases Set.subset_range_enumerate hScount default hbS with ⟨n, rfl⟩
    have he_le_u : e n ≤ u n := prop_2_2_2_1 (he_wayBelow_u n)
    exact le_trans he_le_u
      (le_trans (DirectedSet.le_cumulativeUpper_self hA u hu_mem n) (hs.1 ⟨n, rfl⟩))
  · intro y hy
    refine hs.2 y ?_
    intro x hx
    rcases hx with ⟨n, rfl⟩
    exact hy (DirectedSet.cumulativeUpper_mem hA u hu_mem n)

/-- Compatibility theorem for the older ordinary compact-basis interface. -/
theorem omega_algebraic_dcpo_of_countable_wayBelow_basis
    (hω : IsOmegaCcpo α) (halg : IsOmegaAlgebraicDomain α) :
    IsDcpo α ∧ IsAlgebraicDomain α := by
  exact ⟨omega_ccpo_dcpo_of_countable_wayBelow_basis hω
    ⟨CompactSet, halg.1, halg.2⟩, halg.2⟩

/-- Proposition 2.2.14(3): ω-continuous maps between continuous ω-ccpos are
Scott-continuous. -/
theorem omega_continuous_maps_are_continuous_of_countable_wayBelow_basis
    {β : Type v} [Preorder β] (hcα : IsOmegaContinuousDomain α)
    {f : α → β} (hf : OmegaContinuousMap f) :
    ScottContinuous f := by
  rcases hcα with ⟨B, hBcount, hBraw⟩
  constructor
  · exact hf.1
  · intro A s hA hs
    rcases prop_2_2_13_countable_basis_has_cofinal_omega_chain
        hBcount hBraw hA hs with
      ⟨c, hcmono, hcA, hcsup⟩
    have hfsup : IsSup (f '' Set.range c) (f s) := hf.2 hcmono hcsup
    constructor
    · intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      exact hf.1 (hs.1 ha)
    · intro y hy
      refine hfsup.2 y ?_
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      rcases hx with ⟨n, rfl⟩
      exact hy ⟨c n, hcA n, rfl⟩

/-- Proposition 2.2.14(1): every continuous omega-ccpo is a continuous dcpo. -/
theorem prop_2_2_14_1_continuous_omega_ccpo_dcpo
    (hD : IsContinuousOmegaCcpo α) :
    IsContinuousDcpo α := by
  rcases hD.2 with ⟨B, _hBcount, hB⟩
  have hDcpo : IsDcpo α := by
    intro A hA
    rcases continuousOmegaCcpo_directed_has_cofinal_omegaChain hD hA with
      ⟨_c, _hcmono, _hcA, s, hsA, _hcs⟩
    exact ⟨s, hsA⟩
  exact ⟨⟨hDcpo, hD.1.2⟩, ⟨B, isBasisRaw_of_isOmegaBasis hD hB⟩⟩

/-- Proposition 2.2.14(2): every algebraic omega-ccpo is an algebraic dcpo. -/
theorem prop_2_2_14_2_algebraic_omega_ccpo_dcpo
    (hD : IsAlgebraicOmegaCcpo α) :
    IsAlgebraicDcpo α := by
  let hContinuous : IsContinuousOmegaCcpo α :=
    ⟨hD.1, OmegaCompactSet, hD.2.1, hD.2.2⟩
  have hContinuousDcpo :=
    prop_2_2_14_1_continuous_omega_ccpo_dcpo hContinuous
  have hCompactEq : (OmegaCompactSet : Set α) = CompactSet := by
    ext x
    exact omegaWayBelow_iff_wayBelow hContinuous
  refine ⟨hContinuousDcpo.1, ?_⟩
  change IsBasisRaw (CompactSet : Set α)
  rw [← hCompactEq]
  exact isBasisRaw_of_isOmegaBasis hContinuous hD.2.2

/-- Proposition 2.2.14(3): omega-continuous maps between continuous
omega-ccpos are Scott-continuous. -/
theorem prop_2_2_14_3_omega_continuous_maps_are_continuous
    {β : Type v} [Preorder β]
    (hα : IsContinuousOmegaCcpo α) (_hβ : IsContinuousOmegaCcpo β)
    {f : α → β} (hf : OmegaContinuousMap f) :
    ScottContinuous f := by
  rcases hα.2 with ⟨B, hBcount, hB⟩
  exact omega_continuous_maps_are_continuous_of_countable_wayBelow_basis
    ⟨B, hBcount, isBasisRaw_of_isOmegaBasis hα hB⟩ hf

/-- In a continuous domain, the set `↓↓x` is directed. -/
theorem continuous_wayBelowLower_directed
    (hcont : IsContinuousDomain α) (x : α) :
    DirectedSet (wayBelowLower x) := by
  have hBasis : IsBasis (Set.univ : Set α) := prop_2_2_7_1.mp hcont
  have hdir : DirectedSet (Approximants (Set.univ : Set α) x) := (hBasis x).1
  constructor
  · rcases hdir.1 with ⟨a, ha⟩
    exact ⟨a, ha.2⟩
  · intro a ha b hb
    rcases hdir.2 (x := a) (by exact ⟨Set.mem_univ a, ha⟩)
        (y := b) (by exact ⟨Set.mem_univ b, hb⟩) with
      ⟨c, hc, hac, hbc⟩
    exact ⟨c, hc.2, hac, hbc⟩

/-- In a continuous domain, `x` is the supremum of `↓↓x`. -/
theorem continuous_wayBelowLower_isSup
    (hcont : IsContinuousDomain α) (x : α) :
    IsSup (wayBelowLower x) x := by
  have hBasis : IsBasis (Set.univ : Set α) := prop_2_2_7_1.mp hcont
  have hsup : IsSup (Approximants (Set.univ : Set α) x) x := (hBasis x).2
  constructor
  · intro a ha
    exact prop_2_2_2_1 ha
  · intro y hy
    exact hsup.2 y (by
      intro a ha
      exact hy ha.2)

/-- Two-step approximants of `x`: elements way-below some element way-below
`x`.  This is the standard proof device for the interpolation lemma. -/
def twoStepApproximants (x : α) : Set α :=
  {a | ∃ b : α, a ≪ b ∧ b ≪ x}

/-- In a continuous domain, two-step approximants are directed. -/
theorem continuous_twoStepApproximants_directed
    (hcont : IsContinuousDomain α) (x : α) :
    DirectedSet (twoStepApproximants x) := by
  have hLowerDir : DirectedSet (wayBelowLower x) :=
    continuous_wayBelowLower_directed hcont x
  constructor
  · rcases hLowerDir.1 with ⟨b, hbx⟩
    have hbLowerDir : DirectedSet (wayBelowLower b) :=
      continuous_wayBelowLower_directed hcont b
    rcases hbLowerDir.1 with ⟨a, hab⟩
    exact ⟨a, ⟨b, hab, hbx⟩⟩
  · intro a ha c hc
    rcases ha with ⟨a', haa', ha'x⟩
    rcases hc with ⟨c', hcc', hc'x⟩
    rcases hLowerDir.2 ha'x hc'x with ⟨b, hbx, ha'b, hc'b⟩
    have hab : a ≪ b := prop_2_2_2_2 le_rfl haa' ha'b
    have hcb : c ≪ b := prop_2_2_2_2 le_rfl hcc' hc'b
    have hbLowerDir : DirectedSet (wayBelowLower b) :=
      continuous_wayBelowLower_directed hcont b
    have hbLowerSup : IsSup (wayBelowLower b) b :=
      continuous_wayBelowLower_isSup hcont b
    rcases hab hbLowerDir hbLowerSup le_rfl with ⟨ua, hua, haua⟩
    rcases hcb hbLowerDir hbLowerSup le_rfl with ⟨uc, huc, hcuc⟩
    rcases hbLowerDir.2 hua huc with ⟨d, hdb, huad, hucd⟩
    exact ⟨d, ⟨b, hdb, hbx⟩, le_trans haua huad, le_trans hcuc hucd⟩

/-- In a continuous domain, `x` is the supremum of its two-step approximants. -/
theorem continuous_twoStepApproximants_isSup
    (hcont : IsContinuousDomain α) (x : α) :
    IsSup (twoStepApproximants x) x := by
  have hLowerSup : IsSup (wayBelowLower x) x :=
    continuous_wayBelowLower_isSup hcont x
  constructor
  · intro a ha
    rcases ha with ⟨b, hab, hbx⟩
    exact le_trans (prop_2_2_2_1 hab) (prop_2_2_2_1 hbx)
  · intro y hy
    exact hLowerSup.2 y (by
      intro b hbx
      have hbLowerSup : IsSup (wayBelowLower b) b :=
        continuous_wayBelowLower_isSup hcont b
      exact hbLowerSup.2 y (by
        intro a hab
        exact hy ⟨b, hab, hbx⟩))

/-- Lemma 2.2.15, singleton form: way-below is interpolating in continuous
domains. -/
theorem wayBelow_interpolation
    (hcont : IsContinuousDomain α) {x y : α} (hxy : x ≪ y) :
    ∃ z : α, x ≪ z ∧ z ≪ y := by
  have hdir : DirectedSet (twoStepApproximants y) :=
    continuous_twoStepApproximants_directed hcont y
  have hsup : IsSup (twoStepApproximants y) y :=
    continuous_twoStepApproximants_isSup hcont y
  rcases hxy hdir hsup le_rfl with ⟨a, ha, hxa⟩
  rcases ha with ⟨z, haz, hzy⟩
  exact ⟨z, prop_2_2_2_2 hxa haz le_rfl, hzy⟩

/-- Lemma 2.2.15: interpolation for finite sets of approximants. -/
theorem lemma_2_2_15_interpolation
    (hcont : IsContinuousDomain α) {M : Set α} {y : α}
    (hMfin : M.Finite) (hMy : ∀ m ∈ M, m ≪ y) :
    ∃ y' : α, (∀ m ∈ M, m ≪ y') ∧ y' ≪ y := by
  classical
  have hLowerDir : DirectedSet (wayBelowLower y) :=
    continuous_wayBelowLower_directed hcont y
  rcases hLowerDir.1 with ⟨default, hdefault⟩
  have hChoice : ∀ m ∈ M, ∃ a ∈ wayBelowLower y, m ≪ a := by
    intro m hm
    rcases wayBelow_interpolation hcont (hMy m hm) with ⟨a, hma, hay⟩
    exact ⟨a, hay, hma⟩
  let pick : α → α := fun m =>
    if hm : m ∈ M then Classical.choose (hChoice m hm) else default
  have hpick_mem : ∀ m ∈ M, pick m ∈ wayBelowLower y := by
    intro m hm
    dsimp [pick]
    simp [hm, (Classical.choose_spec (hChoice m hm)).1]
  have hpick_wayBelow : ∀ m ∈ M, m ≪ pick m := by
    intro m hm
    dsimp [pick]
    simp [hm, (Classical.choose_spec (hChoice m hm)).2]
  let F : Set α := pick '' M
  have hFfin : F.Finite := hMfin.image pick
  have hFsub : F ⊆ wayBelowLower y := by
    intro a ha
    rcases ha with ⟨m, hm, rfl⟩
    exact hpick_mem m hm
  rcases DirectedSet.exists_upper_finite hLowerDir hFfin hFsub with
    ⟨y', hy'y, hUpper⟩
  refine ⟨y', ?_, hy'y⟩
  intro m hm
  exact prop_2_2_2_2 le_rfl (hpick_wayBelow m hm)
    (hUpper (pick m) ⟨m, hm, rfl⟩)

/-- Lemma 2.2.15: interpolation can choose from a basis. -/
theorem lemma_2_2_15_interpolation_basis
    {B : Set α} (hB : IsBasis B) {M : Set α} {y : α}
    (hMfin : M.Finite) (hMy : ∀ m ∈ M, m ≪ y) :
    ∃ y' ∈ B, (∀ m ∈ M, m ≪ y') ∧ y' ≪ y := by
  rcases lemma_2_2_15_interpolation ⟨B, basis_to_raw hB⟩ hMfin hMy with
    ⟨y', hMy', hy'y⟩
  have hdir : DirectedSet (Approximants B y) := (hB y).1
  have hsup : IsSup (Approximants B y) y := (hB y).2
  rcases hy'y hdir hsup le_rfl with ⟨b, hb, hy'b⟩
  refine ⟨b, hb.1, ?_, hb.2⟩
  intro m hm
  exact prop_2_2_2_2 le_rfl (hMy' m hm) hy'b

/-- A finite family way-below `y` has a common upper approximant from any basis
of `y`. -/
theorem finite_wayBelow_basis_upper
    {B : Set α} (hB : IsBasis B) {M : Set α} {y : α}
    (hMfin : M.Finite) (hMy : ∀ m ∈ M, m ≪ y) :
    ∃ b ∈ Approximants B y, ∀ m ∈ M, m ≤ b := by
  have hdir : DirectedSet (Approximants B y) := (hB y).1
  have hsup : IsSup (Approximants B y) y := (hB y).2
  exact DirectedSet.exists_upper_finite_of_forall hdir hMfin (by
    intro m hm
    rcases hMy m hm hdir hsup le_rfl with ⟨b, hb, hmb⟩
    exact ⟨b, hb, hmb⟩)

/-- Corollary 2.2.16: way-below elements of a directed supremum already
approximate some member of the directed set. -/
theorem cor_2_2_16_wayBelow_directed_sup
    (hcont : IsContinuousDomain α) {A : Set α} {s c : α}
    (hA : DirectedSet A) (hs : IsSup A s) (hc : c ≪ s) :
    ∃ a ∈ A, c ≪ a := by
  rcases lemma_2_2_15_interpolation hcont (M := ({c} : Set α)) (Set.finite_singleton c)
      (by
        intro m hm
        have hmc : m = c := by simpa using hm
        simpa [hmc] using hc) with
    ⟨c', hcbelow, hc's⟩
  rcases hc's hA hs le_rfl with ⟨a, ha, hc'a⟩
  exact ⟨a, ha, prop_2_2_2_2 le_rfl (hcbelow c (by simp)) hc'a⟩

/-- Corollary 2.2.16: formula `↓↓ sup A = ⋃ a ∈ A, ↓↓a`. -/
theorem cor_2_2_16_wayBelowLower_directed_sup
    (hcont : IsContinuousDomain α) {A : Set α} {s : α}
    (hA : DirectedSet A) (hs : IsSup A s) :
    wayBelowLower s = ⋃ a ∈ A, wayBelowLower a := by
  ext c
  constructor
  · intro hc
    rcases cor_2_2_16_wayBelow_directed_sup hcont hA hs hc with ⟨a, ha, hca⟩
    rw [Set.mem_iUnion]
    exact ⟨a, by rw [Set.mem_iUnion]; exact ⟨ha, hca⟩⟩
  · intro hc
    rw [Set.mem_iUnion] at hc
    rcases hc with ⟨a, harest⟩
    rw [Set.mem_iUnion] at harest
    rcases harest with ⟨ha, hca⟩
    exact prop_2_2_2_2 le_rfl hca (hs.1 ha)

/-- Principal ideals as ordered subtypes. -/
def PrincipalIdealCarrier (x : α) : Type u :=
  {y : α // y ≤ x}

instance principalIdealCarrierPreorder (x : α) : Preorder (PrincipalIdealCarrier x) :=
  inferInstanceAs (Preorder {y : α // y ≤ x})

/-- A directed supremum computed in a principal ideal is also the ambient
directed supremum, provided the ambient preorder is a dcpo. -/
theorem principalIdeal_isSup_to_ambient
    (hD : IsDcpo α) {z : α} {A : Set (PrincipalIdealCarrier z)}
    {s : PrincipalIdealCarrier z}
    (hA : DirectedSet A) (hs : IsSup A s) :
    IsSup (Subtype.val '' A) s.1 := by
  have hImageDir : DirectedSet (Subtype.val '' A) :=
    DirectedSet.image (by
      intro x y hxy
      exact hxy) hA
  rcases hD (Subtype.val '' A) hImageDir with ⟨t, ht⟩
  have htz : t ≤ z := ht.2 z (by
    intro a ha
    rcases ha with ⟨a', _ha'A, rfl⟩
    exact a'.2)
  have hst : s.1 ≤ t := hs.2 ⟨t, htz⟩ (by
    intro a ha
    exact ht.1 ⟨a, ha, rfl⟩)
  constructor
  · intro a ha
    rcases ha with ⟨a', ha'A, rfl⟩
    exact hs.1 ha'A
  · intro y hy
    exact le_trans hst (ht.2 y (by
      intro a ha
      exact hy ha))

/-- Ambient way-below restricts to any principal ideal containing both
endpoints. -/
theorem principalIdeal_wayBelow_of_ambient
    (hD : IsDcpo α) {z x y : α} (hxz : x ≤ z) (hyz : y ≤ z)
    (hxy : x ≪ y) :
    (⟨x, hxz⟩ : PrincipalIdealCarrier z) ≪ ⟨y, hyz⟩ := by
  intro A s hA hs hys
  have hsAmbient : IsSup (Subtype.val '' A) s.1 :=
    principalIdeal_isSup_to_ambient hD hA hs
  rcases hxy (DirectedSet.image (by
      intro a b hab
      exact hab) hA) hsAmbient hys with
    ⟨a, ha, hxa⟩
  rcases ha with ⟨a', ha'A, rfl⟩
  exact ⟨a', ha'A, hxa⟩

/-- A directed set with supremum `y` can be lifted to any principal ideal whose
top lies above `y`. -/
theorem principalIdeal_lift_isSup
    {z y : α} (hyz : y ≤ z) {A : Set α} (hs : IsSup A y) :
    IsSup ({a : PrincipalIdealCarrier z | a.1 ∈ A})
      (⟨y, hyz⟩ : PrincipalIdealCarrier z) := by
  constructor
  · intro a ha
    exact hs.1 ha
  · intro b hb
    exact hs.2 b.1 (by
      intro a ha
      have haz : a ≤ z := le_trans (hs.1 ha) hyz
      exact hb (a := (⟨a, haz⟩ : PrincipalIdealCarrier z)) ha)

/-- Principal-ideal way-below implies the exact ambient supremum test.  This is
the non-circular part of the local-to-global argument: if the ambient directed
set has supremum exactly `y`, then all of its elements already lie in `↓z`. -/
theorem principalIdeal_wayBelow_to_exact_ambient
    {z x y : α} (hxz : x ≤ z) (hyz : y ≤ z)
    (hxy : (⟨x, hxz⟩ : PrincipalIdealCarrier z) ≪ ⟨y, hyz⟩) :
    ∀ ⦃A : Set α⦄, DirectedSet A → IsSup A y → ∃ a ∈ A, x ≤ a := by
  intro A hA hAy
  have hLiftDir : DirectedSet ({a : PrincipalIdealCarrier z | a.1 ∈ A}) := by
    constructor
    · rcases hA.1 with ⟨a, ha⟩
      have haz : a ≤ z := le_trans (hAy.1 ha) hyz
      exact ⟨⟨a, haz⟩, ha⟩
    · intro a ha b hb
      rcases hA.2 (x := a.1) ha (y := b.1) hb with ⟨c, hc, hac, hbc⟩
      have hcz : c ≤ z := le_trans (hAy.1 hc) hyz
      exact ⟨⟨c, hcz⟩, hc, hac, hbc⟩
  have hLiftSup : IsSup ({a : PrincipalIdealCarrier z | a.1 ∈ A})
      (⟨y, hyz⟩ : PrincipalIdealCarrier z) :=
    principalIdeal_lift_isSup hyz hAy
  rcases hxy hLiftDir hLiftSup le_rfl with ⟨a, ha, hxa⟩
  exact ⟨a.1, ha, hxa⟩

/-- If all principal ideals are continuous, local way-below in any principal
ideal is ambient way-below.  The proof tests an arbitrary ambient directed
supremum inside the principal ideal generated by that supremum. -/
theorem principalIdeal_wayBelow_to_ambient_of_principal_continuous
    (hD : IsDcpo α)
    (hPrincipal : ∀ z : α, IsContinuousDomain (PrincipalIdealCarrier z))
    {z x y : α} (hxz : x ≤ z) (hyz : y ≤ z)
    (hxy : (⟨x, hxz⟩ : PrincipalIdealCarrier z) ≪ ⟨y, hyz⟩) :
    x ≪ y := by
  intro A s hA hs hys
  let yInS : PrincipalIdealCarrier s := ⟨y, hys⟩
  let B : Set (PrincipalIdealCarrier s) :=
    Approximants (Set.univ : Set (PrincipalIdealCarrier s)) yInS
  have hBasisS : IsBasis (Set.univ : Set (PrincipalIdealCarrier s)) :=
    prop_2_2_7_1.mp (hPrincipal s)
  have hBdir : DirectedSet B := (hBasisS yInS).1
  have hBsup : IsSup B yInS := (hBasisS yInS).2
  have hBsupAmbient : IsSup (Subtype.val '' B) y :=
    principalIdeal_isSup_to_ambient hD hBdir hBsup
  have hExact := principalIdeal_wayBelow_to_exact_ambient hxz hyz hxy
  rcases hExact (DirectedSet.image (by
      intro a b hab
      exact hab) hBdir) hBsupAmbient with
    ⟨b, hb, hxb⟩
  rcases hb with ⟨b', hbB, rfl⟩
  have hLiftDirA : DirectedSet ({a : PrincipalIdealCarrier s | a.1 ∈ A}) := by
    constructor
    · rcases hA.1 with ⟨a, ha⟩
      have has : a ≤ s := hs.1 ha
      exact ⟨⟨a, has⟩, ha⟩
    · intro a ha b hb
      rcases hA.2 (x := a.1) ha (y := b.1) hb with ⟨c, hc, hac, hbc⟩
      have hcs : c ≤ s := hs.1 hc
      exact ⟨⟨c, hcs⟩, hc, hac, hbc⟩
  have hLiftSupA : IsSup ({a : PrincipalIdealCarrier s | a.1 ∈ A})
      (⟨s, le_rfl⟩ : PrincipalIdealCarrier s) :=
    principalIdeal_lift_isSup le_rfl hs
  rcases hbB.2 hLiftDirA hLiftSupA hys with ⟨a, ha, hba⟩
  exact ⟨a.1, ha, le_trans hxb hba⟩

/-- Proposition 2.2.17(1): in continuous domains, approximation may test only
directed sets whose supremum is exactly the target. -/
theorem prop_2_2_17_1_wayBelow_exact_sup
    (hcont : IsContinuousDomain α) {x y : α} :
    x ≪ y ↔
      ∀ ⦃A : Set α⦄, DirectedSet A → IsSup A y → ∃ a ∈ A, x ≤ a := by
  constructor
  · intro hxy A hA hAy
    exact hxy hA hAy le_rfl
  · intro hExact A s hA hs hys
    have hBasis : IsBasis (Set.univ : Set α) := prop_2_2_7_1.mp hcont
    have hdir : DirectedSet (Approximants (Set.univ : Set α) y) := (hBasis y).1
    have hsup : IsSup (Approximants (Set.univ : Set α) y) y := (hBasis y).2
    rcases hExact hdir hsup with ⟨b, hb, hxb⟩
    have hbs : b ≪ s := prop_2_2_2_2 le_rfl hb.2 hys
    rcases hbs hA hs le_rfl with ⟨a, ha, hba⟩
    exact ⟨a, ha, le_trans hxb hba⟩

/-- Proposition 2.2.17(2): approximation is local to principal ideals. -/
theorem prop_2_2_17_2_wayBelow_principal_ideals
    (hD : IsDcpo α) (hcont : IsContinuousDomain α) {x y : α} :
    x ≪ y ↔
      ∃ z : α, ∃ hxz : x ≤ z, ∃ hyz : y ≤ z,
        (⟨x, hxz⟩ : PrincipalIdealCarrier z) ≪ ⟨y, hyz⟩ := by
  constructor
  · intro hxy
    exact ⟨y, prop_2_2_2_1 hxy, le_rfl,
      principalIdeal_wayBelow_of_ambient hD (prop_2_2_2_1 hxy) le_rfl hxy⟩
  · intro h
    rcases h with ⟨z, hxz, hyz, hxyLocal⟩
    apply (prop_2_2_17_1_wayBelow_exact_sup hcont).2
    intro A hA hAy
    have hLiftSup : IsSup ({a : PrincipalIdealCarrier z | a.1 ∈ A})
        (⟨y, hyz⟩ : PrincipalIdealCarrier z) :=
      principalIdeal_lift_isSup hyz hAy
    have hLiftDir : DirectedSet ({a : PrincipalIdealCarrier z | a.1 ∈ A}) := by
      constructor
      · rcases hA.1 with ⟨a, ha⟩
        have haz : a ≤ z := le_trans (hAy.1 ha) hyz
        exact ⟨⟨a, haz⟩, ha⟩
      · intro a ha b hb
        rcases hA.2 (x := a.1) ha (y := b.1) hb with ⟨c, hc, hac, hbc⟩
        have hcz : c ≤ z := le_trans (hAy.1 hc) hyz
        exact ⟨⟨c, hcz⟩, hc, hac, hbc⟩
    rcases hxyLocal hLiftDir hLiftSup le_rfl with ⟨a, ha, hxa⟩
    exact ⟨a, ha, hxa⟩

/-- Proposition 2.2.17(3), forward direction: a continuous dcpo has continuous
principal ideals. -/
theorem principalIdeal_continuous_of_continuous
    (hD : IsDcpo α) (hcont : IsContinuousDomain α) :
    ∀ z : α, IsContinuousDomain (PrincipalIdealCarrier z) := by
  intro z
  refine ⟨Set.univ, ?_⟩
  intro y
  let A : Set (PrincipalIdealCarrier z) := {a | a.1 ≪ y.1}
  refine ⟨A, ?_, ?_, ?_⟩
  · intro a ha
    exact ⟨Set.mem_univ a,
      principalIdeal_wayBelow_of_ambient hD a.2 y.2 ha⟩
  · have hAmbientDir : DirectedSet (wayBelowLower y.1) :=
      continuous_wayBelowLower_directed hcont y.1
    constructor
    · rcases hAmbientDir.1 with ⟨a, ha⟩
      have haz : a ≤ z := le_trans (prop_2_2_2_1 ha) y.2
      exact ⟨⟨a, haz⟩, ha⟩
    · intro a ha b hb
      rcases hAmbientDir.2 (x := a.1) ha (y := b.1) hb with
        ⟨c, hc, hac, hbc⟩
      have hcz : c ≤ z := le_trans (prop_2_2_2_1 hc) y.2
      exact ⟨⟨c, hcz⟩, hc, hac, hbc⟩
  · have hAmbientSup : IsSup (wayBelowLower y.1) y.1 :=
      continuous_wayBelowLower_isSup hcont y.1
    constructor
    · intro a ha
      exact prop_2_2_2_1 (α := α) (by simpa [A] using ha)
    · intro b hb
      exact hAmbientSup.2 b.1 (by
        intro a ha
        have haz : a ≤ z := le_trans (prop_2_2_2_1 ha) y.2
        exact hb (a := (⟨a, haz⟩ : PrincipalIdealCarrier z)) ha)

/-- Proposition 2.2.17(3): a dcpo is continuous iff all principal ideals are. -/
theorem prop_2_2_17_3_continuous_principal_ideals
    (hD : IsDcpo α) :
    IsContinuousDomain α ↔
      ∀ x : α, IsContinuousDomain (PrincipalIdealCarrier x) := by
  constructor
  · exact principalIdeal_continuous_of_continuous hD
  · intro hPrincipal
    refine ⟨Set.univ, ?_⟩
    intro y
    let yy : PrincipalIdealCarrier y := ⟨y, le_rfl⟩
    let B : Set (PrincipalIdealCarrier y) :=
      Approximants (Set.univ : Set (PrincipalIdealCarrier y)) yy
    have hBasisY : IsBasis (Set.univ : Set (PrincipalIdealCarrier y)) :=
      prop_2_2_7_1.mp (hPrincipal y)
    refine ⟨Subtype.val '' B, ?_, ?_, ?_⟩
    · intro x hx
      rcases hx with ⟨a, ha, rfl⟩
      exact ⟨Set.mem_univ a.1,
        principalIdeal_wayBelow_to_ambient_of_principal_continuous
          hD hPrincipal a.2 le_rfl ha.2⟩
    · exact DirectedSet.image (by
        intro a b hab
        exact hab) (hBasisY yy).1
    · exact principalIdeal_isSup_to_ambient hD (hBasisY yy).1 (hBasisY yy).2

/-- Proposition 2.2.17(4): compact elements are the union of compact elements in
principal ideals. -/
theorem prop_2_2_17_4_compacts_from_principal_ideals
    (hD : IsDcpo α) (hcont : IsContinuousDomain α) :
    CompactSet =
      {x : α | ∃ y : α, ∃ hxy : x ≤ y,
        Compact (⟨x, hxy⟩ : PrincipalIdealCarrier y)} := by
  ext x
  constructor
  · intro hx
    exact ⟨x, le_rfl, principalIdeal_wayBelow_of_ambient hD le_rfl le_rfl hx⟩
  · intro hx
    rcases hx with ⟨y, hxy, hxCompactLocal⟩
    exact (prop_2_2_17_2_wayBelow_principal_ideals hD hcont).2
      ⟨y, hxy, hxy, hxCompactLocal⟩

/-- Proposition 2.2.17(5), forward direction: algebraicity transfers to
principal ideals. -/
theorem principalIdeal_algebraic_of_algebraic
    (hD : IsDcpo α) (halg : IsAlgebraicDomain α) :
    ∀ z : α, IsAlgebraicDomain (PrincipalIdealCarrier z) := by
  intro z y
  rcases halg y.1 with ⟨A, hAcompact, hAdir, hAsup⟩
  let Az : Set (PrincipalIdealCarrier z) := {a | a.1 ∈ A}
  refine ⟨Az, ?_, ?_, ?_⟩
  · intro a ha
    have haApprox := hAcompact ha
    exact ⟨principalIdeal_wayBelow_of_ambient hD a.2 a.2 haApprox.1,
      principalIdeal_wayBelow_of_ambient hD a.2 y.2 haApprox.2⟩
  · constructor
    · rcases hAdir.1 with ⟨a, ha⟩
      have hay : a ≤ y.1 := hAsup.1 ha
      have haz : a ≤ z := le_trans hay y.2
      exact ⟨⟨a, haz⟩, ha⟩
    · intro a ha b hb
      rcases hAdir.2 (x := a.1) ha (y := b.1) hb with ⟨c, hc, hac, hbc⟩
      have hcy : c ≤ y.1 := hAsup.1 hc
      have hcz : c ≤ z := le_trans hcy y.2
      exact ⟨⟨c, hcz⟩, hc, hac, hbc⟩
  · constructor
    · intro a ha
      exact hAsup.1 ha
    · intro b hb
      exact hAsup.2 b.1 (by
        intro a ha
        have hay : a ≤ y.1 := hAsup.1 ha
        have haz : a ≤ z := le_trans hay y.2
        exact hb (a := (⟨a, haz⟩ : PrincipalIdealCarrier z)) ha)

/-- Proposition 2.2.17(5): algebraicity is local to principal ideals. -/
theorem prop_2_2_17_5_algebraic_principal_ideals
    (hD : IsDcpo α) :
    IsAlgebraicDomain α ↔
      ∀ x : α, IsAlgebraicDomain (PrincipalIdealCarrier x) := by
  constructor
  · exact principalIdeal_algebraic_of_algebraic hD
  · intro hPrincipal
    have hPrincipalCont :
        ∀ x : α, IsContinuousDomain (PrincipalIdealCarrier x) := by
      intro x
      exact ⟨CompactSet, hPrincipal x⟩
    have hcont : IsContinuousDomain α :=
      (prop_2_2_17_3_continuous_principal_ideals hD).2 hPrincipalCont
    intro y
    let yy : PrincipalIdealCarrier y := ⟨y, le_rfl⟩
    rcases hPrincipal y yy with ⟨A, hAcompact, hAdir, hAsup⟩
    refine ⟨Subtype.val '' A, ?_, ?_, ?_⟩
    · intro x hx
      rcases hx with ⟨a, ha, rfl⟩
      have hEq := prop_2_2_17_4_compacts_from_principal_ideals hD hcont
      constructor
      · rw [hEq]
        exact ⟨y, a.2, (hAcompact ha).1⟩
      · exact principalIdeal_wayBelow_to_ambient_of_principal_continuous
          hD hPrincipalCont a.2 le_rfl (hAcompact ha).2
    · exact DirectedSet.image (by
        intro a b hab
        exact hab) hAdir
    · exact principalIdeal_isSup_to_ambient hD hAdir hAsup

/-- Proposition 2.2.18(1): minimal upper bounds of finite compact sets are compact
in continuous domains. -/
theorem prop_2_2_18_1_mub_finite_compacts_compact
    (hcont : IsContinuousDomain α) {M : Set α} {u : α}
    (hMfin : M.Finite) (hMcompact : ∀ x ∈ M, Compact x)
    (hu : IsMinimalUpperBound M u) :
    Compact u := by
  have hMu : ∀ m ∈ M, m ≪ u := by
    intro m hm
    exact prop_2_2_2_2 le_rfl (hMcompact m hm) (hu.1 hm)
  rcases hcont with ⟨B, hBraw⟩
  have hB : IsBasis B := prop_2_2_4_1 hBraw
  rcases finite_wayBelow_basis_upper hB hMfin hMu with
    ⟨u', hu'Approx, hMu'⟩
  have hu'Upper : IsUpperBound M u' := by
    intro m hm
    exact hMu' m hm
  have huu' : u ≤ u' := hu.2 hu'Upper (prop_2_2_2_1 hu'Approx.2)
  exact prop_2_2_2_2 huu' hu'Approx.2 le_rfl

/-- Proposition 2.2.18(2): in complete lattices, `↓↓x` is closed under binary joins. -/
theorem prop_2_2_18_2_wayBelowLower_sup_closed
    {L : Type u} [CompleteLattice L] {x a b : L}
    (ha : a ∈ wayBelowLower x) (hb : b ∈ wayBelowLower x) :
    a ⊔ b ∈ wayBelowLower x := by
  intro A s hA hs hxs
  rcases ha hA hs hxs with ⟨a', ha'A, haa'⟩
  rcases hb hA hs hxs with ⟨b', hb'A, hbb'⟩
  rcases hA.2 ha'A hb'A with ⟨c, hcA, ha'c, hb'c⟩
  exact ⟨c, hcA, sup_le (le_trans haa' ha'c) (le_trans hbb' hb'c)⟩

/-- Proposition 2.2.18(3): finite joins of compact elements are compact in
complete lattices. -/
theorem prop_2_2_18_3_finite_join_compact
    {L : Type u} [CompleteLattice L] {M : Set L} {s : L}
    (hMfin : M.Finite) (hMcompact : ∀ x ∈ M, Compact x)
    (hs : IsSup M s) :
    Compact s := by
  intro A t hA ht hst
  have hchoose : ∀ m ∈ M, ∃ a ∈ A, m ≤ a := by
    intro m hm
    exact hMcompact m hm hA ht (le_trans (hs.1 hm) hst)
  rcases hA.exists_upper_finite_of_forall hMfin hchoose with ⟨z, hzA, hzM⟩
  refine ⟨z, hzA, hs.2 z ?_⟩
  intro m hmM
  exact hzM m hmM

/-- Corollary 2.2.19: a complete lattice is algebraic iff every element is a join
of compact elements below it. -/
theorem cor_2_2_19_complete_lattice_algebraic_iff_compact_joins
    {L : Type u} [CompleteLattice L] :
    IsAlgebraicDomain L ↔
      ∀ x : L, IsSup ({k : L | Compact k ∧ k ≤ x} : Set L) x := by
  constructor
  · intro halg x
    rcases halg x with ⟨A, hAsub, _hAdir, hAsup⟩
    constructor
    · intro k hk
      exact hk.2
    · intro y hy
      exact hAsup.2 y (by
        intro a ha
        exact hy ⟨(hAsub ha).1, prop_2_2_2_1 (hAsub ha).2⟩)
  · intro hjoin x
    let Kx : Set L := {k : L | Compact k ∧ k ≤ x}
    have hbotCompact : Compact (⊥ : L) := by
      intro A s hA _hs _hbots
      rcases hA.1 with ⟨a, ha⟩
      exact ⟨a, ha, bot_le⟩
    have hdir : DirectedSet Kx := by
      constructor
      · exact ⟨⊥, hbotCompact, bot_le⟩
      · intro a ha b hb
        have hfin : ({a, b} : Set L).Finite := by
          simpa using (Set.finite_singleton b).insert a
        have hcompact : ∀ z ∈ ({a, b} : Set L), Compact z := by
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · exact ha.1
          · exact hb.1
        have hsup : IsSup ({a, b} : Set L) (a ⊔ b) := by
          constructor
          · intro z hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
            rcases hz with rfl | rfl
            · exact le_sup_left
            · exact le_sup_right
          · intro y hy
            exact sup_le (hy (by simp)) (hy (by simp))
        exact ⟨a ⊔ b,
          ⟨prop_2_2_18_3_finite_join_compact hfin hcompact hsup, sup_le ha.2 hb.2⟩,
          le_sup_left, le_sup_right⟩
    refine ⟨Kx, ?_, hdir, hjoin x⟩
    intro k hk
    exact ⟨hk.1, prop_2_2_2_2 le_rfl hk.1 hk.2⟩

end NumberedCoverageApproximation

end Chapter2
end AbramskyJung

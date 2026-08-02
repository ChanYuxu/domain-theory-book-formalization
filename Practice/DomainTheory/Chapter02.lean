import Practice.DomainTheory.Topology.ScottTopology
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Topology.Defs.Basic

set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-!
# Abramsky--Jung, Domain Theory, Chapter 2: numbered coverage

This book-facing module keeps the numbered Definition/Proposition/Lemma/Theorem/
Corollary declarations for Chapter 2 visible under the original
`AbramskyJung.Chapter2` namespace.  The reusable order-theoretic core now lives
in smaller modules under `Practice.DomainTheory.Order` and
`Practice.DomainTheory.Topology`.

Large results cited to external literature are recorded as documented axioms and
tracked in `formalization_status.md`; the surrounding support lemmas isolate the
proved parts that are reused later.
-/

universe u v w

namespace AbramskyJung
namespace Chapter2

/-!
## Numbered Chapter-2 coverage

The declarations below make every numbered Definition/Proposition/Lemma/Theorem/
Corollary from Chapter 2 visible in Lean.  Large results cited to external
literature are recorded as documented axioms and tracked in
`formalization_status.md`; the surrounding support lemmas isolate the proved
parts that are reused later.
-/

section NumberedCoverageOrder

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Definition 2.1.1: a binary relation is a preorder. -/
def IsPreorderRel (r : α → α → Prop) : Prop :=
  (∀ x : α, r x x) ∧ ∀ ⦃x y z : α⦄, r x y → r y z → r x z

/-- Definition 2.1.1: a binary relation is a partial order. -/
def IsPartialOrderRel (r : α → α → Prop) : Prop :=
  (∀ x : α, r x x) ∧
    (∀ ⦃x y z : α⦄, r x y → r y z → r x z) ∧
      ∀ ⦃x y : α⦄, r x y → r y x → x = y

/-- Proposition 2.1.2: the order-dual of a poset is again a poset. -/
theorem prop_2_1_2_orderDual (α : Type u) [PartialOrder α] :
    Nonempty (PartialOrder αᵒᵈ) := by
  exact ⟨inferInstance⟩

/-- A lower bound computed inside the closed members of a closure system. -/
def ClosureSystem.IsInfClosedFamily
    {α : Type u} (C : ClosureSystem α) (F : Set (Set α)) (I : Set α) : Prop :=
  I ∈ C.closed ∧
    (∀ A ∈ F, I ⊆ A) ∧
      ∀ J ∈ C.closed, (∀ A ∈ F, J ⊆ A) → J ⊆ I

/-- An upper bound computed inside the closed members of a closure system. -/
def ClosureSystem.IsSupClosedFamily
    {α : Type u} (C : ClosureSystem α) (F : Set (Set α)) (S : Set α) : Prop :=
  S ∈ C.closed ∧
    (∀ A ∈ F, A ⊆ S) ∧
      ∀ Z ∈ C.closed, (∀ A ∈ F, A ⊆ Z) → S ⊆ Z

/-- Proposition 2.1.5: the closed members of a closure system form a complete
lattice under inclusion. Intersections compute infima and closure of unions
computes suprema, both relative to the closed carrier. -/
theorem prop_2_1_5_closure_system_complete
    {α : Type u} (C : ClosureSystem α) (F : Set (Set α)) (hF : F ⊆ C.closed) :
    C.IsInfClosedFamily F (⋂₀ F) ∧
      C.IsSupClosedFamily F (C.closure (⋃₀ F)) := by
  constructor
  · refine ⟨C.sInter_closed F hF, ?_, ?_⟩
    · intro A hA x hx
      exact hx A hA
    · intro J hJ hLower x hx A hA
      exact hLower A hA hx
  · refine ⟨C.closure_mem (⋃₀ F), ?_, ?_⟩
    · intro A hA
      exact Set.Subset.trans (by
        intro x hx
        exact ⟨A, hA, hx⟩) C.subset_closure
    · intro Z hZ hUpper
      exact C.closure_sUnion_least_closed_upper_bound hZ hUpper

variable [Preorder α] [Preorder β] [Preorder γ]

/-- Definition 2.1.6: monotone maps. -/
def IsMonotoneMap (f : α → β) : Prop :=
  Monotone f

/-- Definition 2.1.6: identity maps are monotone. -/
theorem IsMonotoneMap.id : IsMonotoneMap (fun x : α => x) := by
  intro x y hxy
  exact hxy

/-- Definition 2.1.6: monotone maps are closed under composition. -/
theorem IsMonotoneMap.comp {f : α → β} {g : β → γ}
    (hg : IsMonotoneMap g) (hf : IsMonotoneMap f) :
    IsMonotoneMap (fun x : α => g (f x)) := by
  intro x y hxy
  exact hg (hf hxy)

/-- Definition 2.1.17: strict maps between pointed dcpos preserve bottom. -/
def StrictMap [OrderBot α] [OrderBot β] (f : α → β) : Prop :=
  f ⊥ = ⊥

/-- Definition 2.1.17: constant maps. -/
def ConstantMap (x : β) : α → β :=
  fun _ => x

theorem StrictMap.id [OrderBot α] : StrictMap (fun x : α => x) :=
  rfl

theorem ConstantMap.monotone (x : β) : IsMonotoneMap (ConstantMap (α := α) x) := by
  intro a b hab
  rfl

/-- Bundled Scott-continuous functions, used for Propositions 2.1.18 and
Theorem 2.1.19(2). -/
structure ScottContFun (α : Type u) (β : Type v) [Preorder α] [Preorder β] where
  toFun : α → β
  continuous : ScottContinuous toFun

namespace ScottContFun

instance : CoeFun (ScottContFun α β) (fun _ => α → β) where
  coe f := f.toFun

instance : Preorder (ScottContFun α β) where
  le f g := ∀ x : α, f x ≤ g x
  le_refl f x := le_rfl
  le_trans f g h hfg hgh x := le_trans (hfg x) (hgh x)

end ScottContFun

/-- Proposition 2.1.7: monotone self-maps on complete lattices have least and
greatest fixed points. -/
theorem prop_2_1_7_complete_lattice_fixpoints
    {L : Type u} [CompleteLattice L] (f : L → L) (hf : Monotone f) :
    ∃ least greatest : L,
      f least = least ∧
      f greatest = greatest ∧
      (∀ y : L, f y = y → least ≤ y) ∧
      (∀ y : L, f y = y → y ≤ greatest) := by
  let A : Set L := {x | f x ≤ x}
  let least : L := sInf A
  have hfleast_le : f least ≤ least := by
    refine le_sInf ?_
    intro x hx
    have hleastx : least ≤ x := sInf_le hx
    exact le_trans (hf hleastx) hx
  have hleast_le_fleast : least ≤ f least := by
    have hfleast_mem : f least ∈ A := hf hfleast_le
    exact sInf_le hfleast_mem
  have hleast_fix : f least = least := le_antisymm hfleast_le hleast_le_fleast
  let B : Set L := {x | x ≤ f x}
  let greatest : L := sSup B
  have hgreatest_le_fgreatest : greatest ≤ f greatest := by
    refine sSup_le ?_
    intro x hx
    have hxgreatest : x ≤ greatest := le_sSup hx
    exact le_trans hx (hf hxgreatest)
  have hfgreatest_le : f greatest ≤ greatest := by
    have hfgreatest_mem : f greatest ∈ B := hf hgreatest_le_fgreatest
    exact le_sSup hfgreatest_mem
  have hgreatest_fix : f greatest = greatest :=
    le_antisymm hfgreatest_le hgreatest_le_fgreatest
  refine ⟨least, greatest, hleast_fix, hgreatest_fix, ?_, ?_⟩
  · intro y hy
    exact sInf_le (by simpa [A, hy])
  · intro y hy
    exact le_sSup (by simpa [B, hy])

/-- Complete lattices are dcpos in the predicate formulation used in this
chapter. -/
theorem completeLattice_isDcpo {L : Type u} [CompleteLattice L] :
    IsDcpo L := by
  intro A _hA
  exact ⟨sSup A, by
    constructor
    · intro a ha
      exact le_sSup ha
    · intro y hy
      exact sSup_le hy⟩

/-- Proposition 2.1.9: finite nonempty partial joins used to decompose a join. -/
def FiniteNonemptyJoinSet (A : Set α) : Set α :=
  {s | ∃ M : Set α, M.Finite ∧ M.Nonempty ∧ M ⊆ A ∧ IsSup M s}

/-- Proposition 2.1.9: the join of a nonempty set in a join-semilattice is the
directed join of joins of finite nonempty subsets. -/
theorem prop_2_1_9_finite_nonempty_join_decomposition
    {A : Set α} {s : α} (_hA : A.Nonempty) (hs : IsSup A s) :
    IsSup (FiniteNonemptyJoinSet A) s := by
  constructor
  · intro t ht
    rcases ht with ⟨M, _hfin, _hne, hsub, hMt⟩
    exact hMt.2 s (by
      intro m hm
      exact hs.1 (hsub hm))
  · intro y hy
    exact hs.2 y (by
      intro a ha
      exact hy ⟨{a}, Set.finite_singleton a, ⟨a, by simp⟩, (by
        intro x hx
        have hxa : x = a := by simpa using hx
        simpa [hxa] using ha), isSup_singleton a⟩)

/-- Definition 2.1.10: monotone nets indexed by directed posets. -/
structure MonotoneNet (I : Type v) (P : Type u) [Preorder I] [Preorder P] where
  directed_index : DirectedSet (Set.univ : Set I)
  toFun : I → P
  monotone : Monotone toFun

/-- Definition 2.1.10: subnets of monotone nets. -/
structure MonotoneNet.Subnet {I : Type v} {P : Type u} [Preorder I] [Preorder P]
    (a : MonotoneNet I P) (J : Type w) [Preorder J] where
  directed_index : DirectedSet (Set.univ : Set J)
  map : J → I
  monotone_map : Monotone map
  cofinal : ∀ i : I, ∃ j : J, i ≤ map j

/-- Definition 2.1.10: a monotone net has a supremum when its image has one. -/
def MonotoneNet.HasSup {I : Type v} {P : Type u} [Preorder I] [Preorder P]
    (a : MonotoneNet I P) (s : P) : Prop :=
  IsSup (Set.range a.toFun) s

/-- Definition 2.1.10: the image of a monotone net is directed. -/
theorem MonotoneNet.range_directed
    {I : Type v} {P : Type u} [Preorder I] [Preorder P]
    (a : MonotoneNet I P) : DirectedSet (Set.range a.toFun) := by
  constructor
  · rcases a.directed_index.1 with ⟨i, _hi⟩
    exact ⟨a.toFun i, ⟨i, rfl⟩⟩
  · intro x hx y hy
    rcases hx with ⟨i, rfl⟩
    rcases hy with ⟨j, rfl⟩
    rcases a.directed_index.2 (x := i) (by simp) (y := j) (by simp) with
      ⟨k, _hk, hik, hjk⟩
    exact ⟨a.toFun k, ⟨k, rfl⟩, a.monotone hik, a.monotone hjk⟩

/-- Definition 2.1.10: `HasSup` unfolds to the supremum of the image set. -/
theorem MonotoneNet.hasSup_iff
    {I : Type v} {P : Type u} [Preorder I] [Preorder P]
    (a : MonotoneNet I P) (s : P) :
    a.HasSup s ↔ IsSup (Set.range a.toFun) s := by
  rfl

/-- Lemma 2.1.11 support: finite subsets of the directed index set form a lattice
with finite principal ideals and provide coherent cofinal upper-bound choices. -/
theorem lemma_2_1_11_finset_index_lattice_cofinal
    {I : Type v} {P : Type u} [Preorder I] [Preorder P]
    (a : MonotoneNet I P) :
    ∃ (J : Type v) (_ : Lattice J), ∃ β : J → I,
      Monotone β ∧
        (∀ i : I, ∃ j : J, i ≤ β j) ∧
        (∀ j : J, ({k : J | k ≤ j} : Set J).Finite) := by
  classical
  let β : Finset I → I := DirectedSet.coherentFinsetUpper a.directed_index
  refine ⟨Finset I, inferInstance, β, ?_, ?_, ?_⟩
  · exact DirectedSet.coherentFinsetUpper_mono a.directed_index
  · intro i
    refine ⟨{i}, ?_⟩
    exact DirectedSet.le_coherentFinsetUpper_of_mem a.directed_index (by simp)
  · intro j
    have hsub : ({k : Finset I | k ≤ j} : Set (Finset I)) ⊆
        (j.powerset : Set (Finset I)) := by
      intro k hk
      exact Finset.mem_powerset.mpr hk
    exact (Finset.finite_toSet j.powerset).subset hsub

/-- Lemma 2.1.11: every monotone net has a subnet whose index set is a lattice
with finite principal ideals. -/
theorem lemma_2_1_11_monotone_net_finite_principal_lattice_subnet
    {I : Type v} {P : Type u} [Preorder I] [Preorder P] (a : MonotoneNet I P) :
    ∃ (J : Type (max u v)) (_ : Lattice J), ∃ β : J → I,
      Monotone β ∧
        (∀ i : I, ∃ j : J, i ≤ β j) ∧
        (∀ j : J, ({k : J | k ≤ j} : Set J).Finite) := by
  classical
  let β : Finset I → I := DirectedSet.coherentFinsetUpper a.directed_index
  refine ⟨ULift.{max u v, v} (Finset I), inferInstance, (fun j => β j.down), ?_, ?_, ?_⟩
  · intro s t hst
    exact DirectedSet.coherentFinsetUpper_mono a.directed_index hst
  · intro i
    refine ⟨ULift.up ({i} : Finset I), ?_⟩
    exact DirectedSet.le_coherentFinsetUpper_of_mem a.directed_index (by simp)
  · intro j
    have hbase : ((j.down.powerset : Finset (Finset I)) : Set (Finset I)).Finite :=
      Finset.finite_toSet j.down.powerset
    have himage : (ULift.up '' ((j.down.powerset : Finset (Finset I)) : Set (Finset I))).Finite :=
      hbase.image ULift.up
    refine himage.subset ?_
    intro k hk
    refine ⟨k.down, ?_, ?_⟩
    · exact Finset.mem_powerset.mpr (by simpa using hk)
    · cases k
      rfl

/-- Proposition 2.1.12: diagonal and iterated directed suprema agree. -/
theorem prop_2_1_12_iterated_directed_suprema
    {I : Type v} [Preorder I] {P : Type u} [PartialOrder P]
    {a : I → I → P} {s d : P}
    (hI : DirectedSet (Set.univ : Set I))
    (ha : Monotone (fun p : I × I => a p.1 p.2))
    (hAll : IsSup (Set.range (fun p : I × I => a p.1 p.2)) s)
    (hDiag : IsSup (Set.range (fun i : I => a i i)) d) :
    s = d := by
  have hDiagAsAll : IsSup (Set.range (fun p : I × I => a p.1 p.2)) d := by
    constructor
    · intro x hx
      rcases hx with ⟨p, rfl⟩
      rcases hI.2 (x := p.1) (by simp) (y := p.2) (by simp) with
        ⟨k, _hk, hpk₁, hpk₂⟩
      have hp_le : p ≤ (k, k) := ⟨hpk₁, hpk₂⟩
      have hkk : a k k ∈ Set.range (fun i : I => a i i) := ⟨k, rfl⟩
      exact le_trans (ha hp_le) (hDiag.1 hkk)
    · intro y hy
      exact hDiag.2 y (by
        intro x hx
        rcases hx with ⟨i, rfl⟩
        exact hy ⟨(i, i), rfl⟩)
  exact IsSup.unique hAll hDiagAsAll

/-- Proposition 2.1.15: having suprema for nonempty chains, using the same
nonempty-chain convention as `IsChainSet`. -/
def HasChainSups (α : Type u) [Preorder α] : Prop :=
  ∀ A : Set α, IsChainSet A → ∃ x : α, IsSup A x

/-- Proposition 2.1.15, easy direction: directed suprema immediately give
suprema for chains, because every chain is directed. -/
theorem dcpo_hasChainSups
    {D : Type u} [PartialOrder D] (hD : IsDcpo D) :
    HasChainSups D := by
  intro A hA
  exact hD A (chain_directed hA)

/-- Proposition 2.1.15 support: a chain inside a directed set which is cofinal
in that set.  Markowsky/Iwamura-style arguments reduce directed suprema to
constructing such chain-cofinal subsets, possibly after transfinite recursion. -/
structure DirectedSet.CofinalChain
    {D : Type u} [Preorder D] (A : Set D) where
  carrier : Set D
  chain : IsChainSet carrier
  subset : carrier ⊆ A
  cofinal : ∀ a ∈ A, ∃ c ∈ carrier, a ≤ c

namespace DirectedSet.CofinalChain

theorem directed
    {D : Type u} [Preorder D] {A : Set D}
    (C : DirectedSet.CofinalChain A) :
    DirectedSet C.carrier :=
  chain_directed C.chain

end DirectedSet.CofinalChain

/-- Proposition 2.1.15 support: a cofinal chain inside a directed set has a
supremum by the chain-supremum hypothesis, and that supremum is also the
supremum of the ambient directed set. -/
theorem chain_sups_directed_sups_of_cofinal_chain
    {D : Type u} [Preorder D] (hChains : HasChainSups D)
    {A : Set D} (C : DirectedSet.CofinalChain A) :
    ∃ s : D, IsSup A s := by
  rcases hChains C.carrier C.chain with ⟨s, hs⟩
  exact ⟨s, IsSup.of_cofinal_subset C.subset C.cofinal hs⟩

/-- Proposition 2.1.15 support: if a directed set has a countable cofinal
sequence, the chain-supremum hypothesis supplies its supremum. -/
theorem chain_sups_directed_sups_of_countable_cofinal
    {D : Type u} [PartialOrder D] (hChains : HasChainSups D)
    {A : Set D} (hA : DirectedSet A) {u : Nat → D}
    (hu : ∀ n : Nat, u n ∈ A)
    (hcofinal : ∀ a ∈ A, ∃ n : Nat, a ≤ u n) :
    ∃ s : D, IsSup A s := by
  let c : Nat → D := DirectedSet.cumulativeUpper hA u hu
  have hcmono : Monotone c := DirectedSet.cumulativeUpper_monotone hA u hu
  have hcchain : IsChainSet (Set.range c) := by
    constructor
    · exact ⟨c 0, ⟨0, rfl⟩⟩
    · intro x hx y hy
      rcases hx with ⟨m, rfl⟩
      rcases hy with ⟨n, rfl⟩
      rcases le_total m n with hmn | hnm
      · exact Or.inl (hcmono hmn)
      · exact Or.inr (hcmono hnm)
  exact chain_sups_directed_sups_of_cofinal_chain hChains
    { carrier := Set.range c
      chain := hcchain
      subset := by
        intro z hz
        rcases hz with ⟨n, rfl⟩
        exact DirectedSet.cumulativeUpper_mem hA u hu n
      cofinal := by
        intro a ha
        rcases hcofinal a ha with ⟨n, hau⟩
        exact ⟨c n, ⟨n, rfl⟩,
          le_trans hau (DirectedSet.le_cumulativeUpper_self hA u hu n)⟩ }

/-- Proposition 2.1.15 support, countable case: a countable directed set can be
enumerated, replaced by the chain of cumulative upper bounds, and then its
supremum follows from the chain-supremum hypothesis. -/
theorem chain_sups_countable_directed_sups
    {D : Type u} [PartialOrder D] (hChains : HasChainSups D)
    {A : Set D} (hA : DirectedSet A) (hCount : A.Countable) :
    ∃ s : D, IsSup A s := by
  classical
  rcases hCount.exists_eq_range hA.1 with ⟨u, hAu⟩
  have hu : ∀ n : Nat, u n ∈ A := by
    intro n
    rw [hAu]
    exact Set.mem_range_self n
  exact chain_sups_directed_sups_of_countable_cofinal hChains hA hu (by
    intro a ha
    have haRange : a ∈ Set.range u := by
      simpa [hAu] using ha
    rcases haRange with ⟨n, rfl⟩
    exact ⟨n, le_rfl⟩)

/-- Proposition 2.1.15 support: an Iwamura/Markowsky decomposition writes a
directed set as the union of a chain of directed subsets.  The literature proof
then applies induction to the pieces and takes the supremum of the resulting
chain of suprema. -/
structure DirectedSet.IwamuraDecomposition
    {D : Type u} [Preorder D] (A : Set D) (ι : Type v) [Preorder ι]
    (F : ι → Set D) : Prop where
  index_chain : IsChainSet (Set.univ : Set ι)
  directed_piece : ∀ i : ι, DirectedSet (F i)
  piece_subset : ∀ i : ι, F i ⊆ A
  monotone_piece : ∀ ⦃i j : ι⦄, i ≤ j → F i ⊆ F j
  covers : ∀ a ∈ A, ∃ i : ι, a ∈ F i

namespace DirectedSet.IwamuraDecomposition

/-- Suprema of the pieces in an Iwamura decomposition are monotone in the
decomposition index. -/
theorem suprema_monotone
    {D : Type u} [Preorder D] {A : Set D}
    {ι : Type v} [Preorder ι] {F : ι → Set D}
    (hDec : DirectedSet.IwamuraDecomposition A ι F)
    {σ : ι → D} (hσSup : ∀ i : ι, IsSup (F i) (σ i)) :
    Monotone σ := by
  intro i j hij
  exact (hσSup i).2 (σ j) (by
    intro x hx
    exact (hσSup j).1 (hDec.monotone_piece hij hx))

/-- Suprema of the pieces in an Iwamura decomposition form a chain. -/
theorem suprema_chain
    {D : Type u} [Preorder D] {A : Set D}
    {ι : Type v} [Preorder ι] {F : ι → Set D}
    (hDec : DirectedSet.IwamuraDecomposition A ι F)
    {σ : ι → D} (hσSup : ∀ i : ι, IsSup (F i) (σ i)) :
    IsChainSet (Set.range σ) := by
  have hσmono : Monotone σ := hDec.suprema_monotone hσSup
  constructor
  · rcases hDec.index_chain.1 with ⟨i, _hi⟩
    exact ⟨σ i, ⟨i, rfl⟩⟩
  · intro x hx y hy
    rcases hx with ⟨i, rfl⟩
    rcases hy with ⟨j, rfl⟩
    rcases hDec.index_chain.2 (x := i) (by simp) (y := j) (by simp) with hij | hji
    · exact Or.inl (hσmono hij)
    · exact Or.inr (hσmono hji)

end DirectedSet.IwamuraDecomposition

/-- Proposition 2.1.15 support: if a directed set is decomposed into a chain of
directed pieces whose suprema already exist, then the supremum of those piece
suprema is the supremum of the original directed set. -/
theorem isSup_of_iwamuraDecomposition_sups
    {D : Type u} [Preorder D] {A : Set D}
    {ι : Type v} [Preorder ι] {F : ι → Set D}
    (hChains : HasChainSups D)
    (hDec : DirectedSet.IwamuraDecomposition A ι F)
    (hSupF : ∀ i : ι, ∃ s : D, IsSup (F i) s) :
    ∃ s : D, IsSup A s := by
  classical
  let σ : ι → D := fun i => Classical.choose (hSupF i)
  have hσSup : ∀ i : ι, IsSup (F i) (σ i) := by
    intro i
    exact Classical.choose_spec (hSupF i)
  have hσchain : IsChainSet (Set.range σ) := hDec.suprema_chain hσSup
  rcases hChains (Set.range σ) hσchain with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  constructor
  · intro a ha
    rcases hDec.covers a ha with ⟨i, hai⟩
    exact le_trans ((hσSup i).1 hai) (hs.1 ⟨i, rfl⟩)
  · intro y hy
    exact hs.2 y (by
      intro z hz
      rcases hz with ⟨i, rfl⟩
      exact (hσSup i).2 y (by
        intro x hx
        exact hy (hDec.piece_subset i hx)))


/-- A predicate-level chain-supremum hypothesis supplies the
`ChainCompletePartialOrder` structure used by mathlib. -/
@[reducible]
noncomputable def chainCompletePartialOrderOfChainSups
    (D : Type u) [PartialOrder D] (hChains : HasChainSups D) :
    ChainCompletePartialOrder D where
  cSup c :=
    Classical.choose (hChains c.carrier
      ⟨c.Nonempty', fun {_x} hx {_y} hy => c.isChain'.total hx hy⟩)
  le_cSup c _x hx :=
    (Classical.choose_spec (hChains c.carrier
      ⟨c.Nonempty', fun {_x} hx {_y} hy => c.isChain'.total hx hy⟩)).1 hx
  cSup_le c x hx :=
    (Classical.choose_spec (hChains c.carrier
      ⟨c.Nonempty', fun {_x} hx {_y} hy => c.isChain'.total hx hy⟩)).2 x hx

/-- A predicate-level dcpo supplies the `ChainCompletePartialOrder` structure used
by mathlib's Bourbaki-Witt theorem. -/
@[reducible]
noncomputable def chainCompletePartialOrderOfDcpo
    (D : Type u) [PartialOrder D] (hD : IsDcpo D) :
    ChainCompletePartialOrder D where
  cSup c :=
    Classical.choose (hD c.carrier (chain_directed
      ⟨c.Nonempty', fun {_x} hx {_y} hy => c.isChain'.total hx hy⟩))
  le_cSup c _x hx :=
    (Classical.choose_spec (hD c.carrier (chain_directed
      ⟨c.Nonempty', fun {_x} hx {_y} hy => c.isChain'.total hx hy⟩))).1 hx
  cSup_le c x hx :=
    (Classical.choose_spec (hD c.carrier (chain_directed
      ⟨c.Nonempty', fun {_x} hx {_y} hy => c.isChain'.total hx hy⟩))).2 x hx

/-- External theorem used in Proposition 2.1.15 (Iwamura [Iwa44],
Markowsky [Mar76]): in the presence of choice, chain-completeness already
supplies directed suprema.  The surrounding file proves several reusable finite,
cofinal-chain, and decomposition reductions, but the full transfinite
Iwamura/Markowsky construction is imported here as an explicitly documented
external assumption under the project rule for theorems cited to external
references. -/
axiom markowsky_dcpo_of_chain_sups
    {D : Type u} [PartialOrder D] (hChains : HasChainSups D) :
    IsDcpo D

/-- Proposition 2.1.15: a poset is a dcpo iff every chain has a supremum. -/
theorem prop_2_1_15_dcpo_iff_chain_sups
    {D : Type u} [PartialOrder D] :
    IsDcpo D ↔ HasChainSups D := by
  exact ⟨dcpo_hasChainSups, markowsky_dcpo_of_chain_sups⟩

/-- Proposition 2.1.16: every monotone self-map has a least fixed point. -/
def HasLeastFixedPoints (α : Type u) [Preorder α] : Prop :=
  ∀ f : α → α, Monotone f →
    ∃ x : α, f x = x ∧ ∀ y : α, f y = y → x ≤ y

/-- A least pre-fixed point of an endomap. -/
def IsLeastPreFixedPoint {α : Type u} [Preorder α] (f : α → α) (x : α) : Prop :=
  f x ≤ x ∧ ∀ y : α, f y ≤ y → x ≤ y

/-- Every monotone endomap has a least pre-fixed point.  For monotone maps this
is equivalent to having a least fixed point, but the pre-fixed formulation is the
standard Tarski/Pataraia intermediate target. -/
def HasLeastPreFixedPoints (α : Type u) [Preorder α] : Prop :=
  ∀ f : α → α, Monotone f → ∃ x : α, IsLeastPreFixedPoint f x

/-- Pataraia's proof target: the set of common lower bounds of all pre-fixed
points of a monotone endomap.  In a pointed dcpo the key Pataraia lemma says
that this set is directed. -/
def pataraiaLowerSet {α : Type u} [Preorder α] (f : α → α) : Set α :=
  {x | ∀ y : α, f y ≤ y → x ≤ y}

theorem bot_mem_pataraiaLowerSet
    {α : Type u} [Preorder α] [OrderBot α] (f : α → α) :
    ⊥ ∈ pataraiaLowerSet f := by
  intro y _hy
  exact bot_le

/-- Pataraia lower bounds are closed under a monotone endomap. -/
theorem pataraiaLowerSet_apply_mem
    {α : Type u} [Preorder α] {f : α → α} (hf : Monotone f)
    {x : α} (hx : x ∈ pataraiaLowerSet f) :
    f x ∈ pataraiaLowerSet f := by
  intro y hy
  exact le_trans (hf (hx y hy)) hy

/-- If the Pataraia lower set has a supremum, then that supremum is the least
pre-fixed point.  The nontrivial Pataraia theorem is therefore exactly the
directedness of this lower set in pointed dcpos. -/
theorem isLeastPreFixedPoint_of_isSup_pataraiaLowerSet
    {α : Type u} [Preorder α] {f : α → α} (hf : Monotone f)
    {s : α} (hs : IsSup (pataraiaLowerSet f) s) :
    IsLeastPreFixedPoint f s := by
  have hsLower : s ∈ pataraiaLowerSet f := by
    intro y hy
    exact hs.2 y (by
      intro x hx
      exact hx y hy)
  constructor
  · exact hs.1 (pataraiaLowerSet_apply_mem hf hsLower)
  · intro y hy
    exact hsLower y hy

/-- A least pre-fixed point is exactly the supremum of the Pataraia lower set:
it is itself a lower bound of all pre-fixed points, and all such lower bounds
lie below it because it is pre-fixed. -/
theorem isSup_pataraiaLowerSet_of_isLeastPreFixedPoint
    {α : Type u} [Preorder α] {f : α → α} {s : α}
    (hs : IsLeastPreFixedPoint f s) :
    IsSup (pataraiaLowerSet f) s := by
  constructor
  · intro x hx
    exact hx s hs.1
  · intro y hy
    exact hy (by
      intro z hz
      exact hs.2 z hz)

/-- For monotone endomaps, being the least pre-fixed point is equivalent to
being the supremum of the Pataraia lower set. -/
theorem isLeastPreFixedPoint_iff_isSup_pataraiaLowerSet
    {α : Type u} [Preorder α] {f : α → α} (hf : Monotone f) {s : α} :
    IsLeastPreFixedPoint f s ↔ IsSup (pataraiaLowerSet f) s := by
  constructor
  · exact isSup_pataraiaLowerSet_of_isLeastPreFixedPoint
  · exact isLeastPreFixedPoint_of_isSup_pataraiaLowerSet hf

/-- Least pre-fixed points are unique in a partial order. -/
theorem IsLeastPreFixedPoint.unique
    {α : Type u} [PartialOrder α] {f : α → α} {x y : α}
    (hx : IsLeastPreFixedPoint f x) (hy : IsLeastPreFixedPoint f y) :
    x = y := by
  exact le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)

/-- The supremum of the Pataraia lower set is unique whenever it exists. -/
theorem isSup_pataraiaLowerSet_unique
    {α : Type u} [PartialOrder α] {f : α → α} {x y : α}
    (hx : IsSup (pataraiaLowerSet f) x)
    (hy : IsSup (pataraiaLowerSet f) y) :
    x = y :=
  IsSup.unique hx hy

/-- A dcpo has least pre-fixed points once the Pataraia lower set is known to be
directed for every monotone endomap. -/
theorem hasLeastPreFixedPoints_of_pataraiaLowerSet_directed
    {α : Type u} [Preorder α] (hD : IsDcpo α)
    (hPataraia : ∀ f : α → α, Monotone f → DirectedSet (pataraiaLowerSet f)) :
    HasLeastPreFixedPoints α := by
  intro f hf
  rcases hD (pataraiaLowerSet f) (hPataraia f hf) with ⟨s, hs⟩
  exact ⟨s, isLeastPreFixedPoint_of_isSup_pataraiaLowerSet hf hs⟩

/-- Existence of least pre-fixed points is equivalent to existence of suprema
for all Pataraia lower sets of monotone endomaps. -/
theorem hasLeastPreFixedPoints_iff_pataraiaLowerSet_sups
    {α : Type u} [Preorder α] :
    HasLeastPreFixedPoints α ↔
      ∀ f : α → α, Monotone f → ∃ s : α, IsSup (pataraiaLowerSet f) s := by
  constructor
  · intro hpre f hf
    rcases hpre f hf with ⟨s, hs⟩
    exact ⟨s, isSup_pataraiaLowerSet_of_isLeastPreFixedPoint hs⟩
  · intro hsup f hf
    rcases hsup f hf with ⟨s, hs⟩
    exact ⟨s, isLeastPreFixedPoint_of_isSup_pataraiaLowerSet hf hs⟩

/-- For a monotone endomap, a least pre-fixed point is a least fixed point. -/
theorem leastPreFixedPoint_isLeastFixedPoint
    {α : Type u} [PartialOrder α] {f : α → α} (hf : Monotone f) {x : α}
    (hx : IsLeastPreFixedPoint f x) :
    f x = x ∧ ∀ y : α, f y = y → x ≤ y := by
  have hfx_pre : f (f x) ≤ f x := hf hx.1
  have hxfx : x ≤ f x := hx.2 (f x) hfx_pre
  refine ⟨le_antisymm hx.1 hxfx, ?_⟩
  intro y hy
  exact hx.2 y hy.le

/-- A least pre-fixed point is the least fixed point of a monotone endomap,
packaged in the local predicate used by Theorem 2.1.19. -/
theorem leastPreFixedPoint_isLeastFixedPoint_pred
    {α : Type u} [PartialOrder α] {f : α → α} (hf : Monotone f) {x : α}
    (hx : IsLeastPreFixedPoint f x) :
    IsLeastFixedPoint f x :=
  leastPreFixedPoint_isLeastFixedPoint hf hx

/-- Least pre-fixed points imply least fixed points for monotone endomaps. -/
theorem hasLeastFixedPoints_of_hasLeastPreFixedPoints
    {α : Type u} [PartialOrder α]
    (hpre : HasLeastPreFixedPoints α) :
    HasLeastFixedPoints α := by
  intro f hf
  rcases hpre f hf with ⟨x, hx⟩
  exact ⟨x, leastPreFixedPoint_isLeastFixedPoint hf hx⟩

/-- Pataraia directedness plus dcpo structure yields least fixed points for all
monotone endomaps. -/
theorem hasLeastFixedPoints_of_pataraiaLowerSet_directed
    {α : Type u} [PartialOrder α] (hD : IsDcpo α)
    (hPataraia : ∀ f : α → α, Monotone f → DirectedSet (pataraiaLowerSet f)) :
    HasLeastFixedPoints α :=
  hasLeastFixedPoints_of_hasLeastPreFixedPoints
    (hasLeastPreFixedPoints_of_pataraiaLowerSet_directed hD hPataraia)

/-- Proposition 2.1.16 support: if a least-fixed-point computation has exactly
the upper bounds of `A` as fixed points, then its least fixed point is the
supremum of `A`. -/
theorem isSup_of_leastFixedPoint_upperBounds
    {D : Type u} [PartialOrder D] {A : Set D} {f : D → D} {x : D}
    (hx : IsLeastFixedPoint f x)
    (hfixed : ∀ y : D, f y = y ↔ IsUpperBound A y) :
    IsSup A x := by
  constructor
  · exact (hfixed x).mp hx.1
  · intro y hy
    exact hx.2 y ((hfixed y).mpr hy)

/-- Proposition 2.1.16 converse support: if every directed set has a monotone
self-map whose fixed points are exactly its upper bounds, then least fixed
points provide directed suprema. -/
theorem isDcpo_of_hasLeastFixedPoints_of_upperBound_fixedPoint_maps
    {D : Type u} [PartialOrder D] (hfix : HasLeastFixedPoints D)
    (hMaps :
      ∀ A : Set D, DirectedSet A →
        ∃ f : D → D, Monotone f ∧ ∀ y : D, f y = y ↔ IsUpperBound A y) :
    IsDcpo D := by
  intro A hA
  rcases hMaps A hA with ⟨f, hfmono, hfixed⟩
  rcases hfix f hfmono with ⟨x, hx⟩
  exact ⟨x, isSup_of_leastFixedPoint_upperBounds hx hfixed⟩

/-- Proposition 2.1.16/Markowsky support: for a well-ordered monotone chain,
send a non-upper-bound `x` to the first chain element not below `x`, and leave
upper bounds fixed. -/
noncomputable def wellOrderedChainUpperBoundMap
    {ι : Type v} {D : Type u} [LinearOrder ι] [WellFoundedLT ι] [Preorder D]
    (c : ι → D) (x : D) : D := by
  classical
  exact
    if h : ∃ i : ι, ¬ c i ≤ x then
      c (wellFounded_lt.min {i : ι | ¬ c i ≤ x} h)
    else x

/-- The well-ordered-chain upper-bound map is monotone. -/
theorem wellOrderedChainUpperBoundMap_monotone
    {ι : Type v} {D : Type u} [LinearOrder ι] [WellFoundedLT ι] [Preorder D]
    {c : ι → D} (hc : Monotone c) :
    Monotone (wellOrderedChainUpperBoundMap c) := by
  classical
  intro x y hxy
  by_cases hx : ∃ i : ι, ¬ c i ≤ x
  · by_cases hy : ∃ i : ι, ¬ c i ≤ y
    · let ix : ι := wellFounded_lt.min {i : ι | ¬ c i ≤ x} hx
      let iy : ι := wellFounded_lt.min {i : ι | ¬ c i ≤ y} hy
      have hiy_mem_y : ¬ c iy ≤ y := by
        simpa [iy] using wellFounded_lt.min_mem {i : ι | ¬ c i ≤ y} hy
      have hiy_mem_x : ¬ c iy ≤ x := by
        intro hle
        exact hiy_mem_y (le_trans hle hxy)
      have hix_le_iy : ix ≤ iy := by
        have hmin :=
          (Classical.choose_spec (wellFounded_lt.has_min
            ({i : ι | ¬ c i ≤ x} : Set ι) hx)).2 iy hiy_mem_x
        change wellFounded_lt.min ({i : ι | ¬ c i ≤ x} : Set ι) hx ≤ iy
        change Classical.choose
          (wellFounded_lt.has_min ({i : ι | ¬ c i ≤ x} : Set ι) hx) ≤ iy
        exact not_lt.mp hmin
      have hmapx :
          wellOrderedChainUpperBoundMap c x = c ix := by
        simp [wellOrderedChainUpperBoundMap, hx, ix]
      have hmapy :
          wellOrderedChainUpperBoundMap c y = c iy := by
        simp [wellOrderedChainUpperBoundMap, hy, iy]
      rw [hmapx, hmapy]
      exact hc hix_le_iy
    · have hyUpper : ∀ i : ι, c i ≤ y := by
        intro i
        by_contra hi
        exact hy ⟨i, hi⟩
      let ix : ι := wellFounded_lt.min {i : ι | ¬ c i ≤ x} hx
      have hmapx :
          wellOrderedChainUpperBoundMap c x = c ix := by
        simp [wellOrderedChainUpperBoundMap, hx, ix]
      have hmapy :
          wellOrderedChainUpperBoundMap c y = y := by
        simp [wellOrderedChainUpperBoundMap, hy]
      rw [hmapx, hmapy]
      exact hyUpper ix
  · have hxUpper : ∀ i : ι, c i ≤ x := by
      intro i
      by_contra hi
      exact hx ⟨i, hi⟩
    have hy : ¬ ∃ i : ι, ¬ c i ≤ y := by
      rintro ⟨i, hi⟩
      exact hi (le_trans (hxUpper i) hxy)
    have hmapx :
        wellOrderedChainUpperBoundMap c x = x := by
      simp [wellOrderedChainUpperBoundMap, hx]
    have hmapy :
        wellOrderedChainUpperBoundMap c y = y := by
      simp [wellOrderedChainUpperBoundMap, hy]
    rw [hmapx, hmapy]
    exact hxy

/-- The fixed points of the well-ordered-chain upper-bound map are exactly the
upper bounds of the chain range. -/
theorem wellOrderedChainUpperBoundMap_fixed_iff
    {ι : Type v} {D : Type u} [LinearOrder ι] [WellFoundedLT ι] [Preorder D]
    {c : ι → D} {x : D} :
    wellOrderedChainUpperBoundMap c x = x ↔ IsUpperBound (Set.range c) x := by
  classical
  constructor
  · intro hx y hy
    rcases hy with ⟨i, rfl⟩
    by_contra hi
    let h : ∃ j : ι, ¬ c j ≤ x := ⟨i, hi⟩
    let j : ι := wellFounded_lt.min {j : ι | ¬ c j ≤ x} h
    have hj : ¬ c j ≤ x := by
      simpa [j] using wellFounded_lt.min_mem {j : ι | ¬ c j ≤ x} h
    have hmap :
        wellOrderedChainUpperBoundMap c x = c j := by
      simp [wellOrderedChainUpperBoundMap, h, j]
    have hcx : c j = x := by
      rw [← hmap]
      exact hx
    exact hj (by rw [hcx])
  · intro hx
    have hnone : ¬ ∃ i : ι, ¬ c i ≤ x := by
      rintro ⟨i, hi⟩
      exact hi (hx ⟨i, rfl⟩)
    simp [wellOrderedChainUpperBoundMap, hnone]

/-- Proposition 2.1.16/Markowsky support: least fixed points supply suprema for
well-ordered monotone chains, using the standard upper-bound fixed-point map. -/
theorem exists_isSup_range_of_hasLeastFixedPoints_wellOrderedChain
    {ι : Type v} {D : Type u} [LinearOrder ι] [WellFoundedLT ι] [PartialOrder D]
    (hfix : HasLeastFixedPoints D) {c : ι → D} (hc : Monotone c) :
    ∃ s : D, IsSup (Set.range c) s := by
  let f : D → D := wellOrderedChainUpperBoundMap c
  have hfmono : Monotone f := wellOrderedChainUpperBoundMap_monotone hc
  rcases hfix f hfmono with ⟨s, hs⟩
  exact ⟨s, isSup_of_leastFixedPoint_upperBounds hs
    (fun y => wellOrderedChainUpperBoundMap_fixed_iff (c := c) (x := y))⟩

/-- Proposition 2.1.16/Markowsky support: a chain equipped with a cofinal
well-ordered monotone parametrization. -/
structure WellOrderedCofinalChain
    {D : Type u} [Preorder D] (A : Set D) where
  index : Type v
  linearOrder : LinearOrder index
  wellFoundedLT : WellFoundedLT index
  chain : index → D
  monotone : (letI : LinearOrder index := linearOrder; Monotone chain)
  subset : Set.range chain ⊆ A
  cofinal : ∀ a ∈ A, ∃ i : index, a ≤ chain i

/-- Proposition 2.1.16/Markowsky support: if every chain has a cofinal
well-ordered monotone parametrization, then least fixed points supply all chain
suprema.  The remaining Markowsky step is the choice-theoretic construction of
such cofinal well-ordered chains. -/
theorem hasChainSups_of_hasLeastFixedPoints_of_wellOrderedCofinalChains
    {D : Type u} [PartialOrder D] (hfix : HasLeastFixedPoints D)
    (hCofinal :
      ∀ A : Set D, IsChainSet A → Nonempty (WellOrderedCofinalChain.{u, v} A)) :
    HasChainSups D := by
  intro A hA
  rcases hCofinal A hA with ⟨C⟩
  letI : LinearOrder C.index := C.linearOrder
  letI : WellFoundedLT C.index := C.wellFoundedLT
  have hcmono : Monotone C.chain := C.monotone
  rcases exists_isSup_range_of_hasLeastFixedPoints_wellOrderedChain hfix hcmono with
    ⟨s, hs⟩
  have hcofinalRange :
      ∀ a ∈ A, ∃ b ∈ Set.range C.chain, a ≤ b := by
    intro a ha
    rcases C.cofinal a ha with ⟨i, hai⟩
    exact ⟨C.chain i, ⟨i, rfl⟩, hai⟩
  exact ⟨s, IsSup.of_cofinal_subset C.subset hcofinalRange hs⟩

/-- Proposition 2.1.7 support: complete lattices satisfy the local
least-fixed-point predicate for all monotone endomaps. -/
theorem completeLattice_hasLeastFixedPoints
    {L : Type u} [CompleteLattice L] :
    HasLeastFixedPoints L := by
  intro f hf
  rcases prop_2_1_7_complete_lattice_fixpoints f hf with
    ⟨least, _greatest, hleast, _hgreatest, hleast_le, _hgreatest_le⟩
  exact ⟨least, hleast, hleast_le⟩

/-- Complete lattices have least pre-fixed points for all monotone endomaps. -/
theorem completeLattice_hasLeastPreFixedPoints
    {L : Type u} [CompleteLattice L] :
    HasLeastPreFixedPoints L := by
  intro f hf
  let A : Set L := {x | f x ≤ x}
  let least : L := sInf A
  have hfleast_le : f least ≤ least := by
    refine le_sInf ?_
    intro x hx
    have hleastx : least ≤ x := sInf_le hx
    exact le_trans (hf hleastx) hx
  exact ⟨least, hfleast_le, fun y hy => sInf_le (by simpa [A] using hy)⟩

/-- Proposition 2.1.16 support: Bourbaki-Witt gives fixed points for progressive
endomaps once a predicate-level dcpo has been bridged to mathlib's chain-complete
order structure.  The full arbitrary-monotone least-fixed-point equivalence is
recorded below as the documented external Markowsky/Pataraia theorem. -/
theorem dcpo_inflationary_endomap_has_fixed_point
    {D : Type u} [PartialOrder D] [OrderBot D]
    (hD : IsDcpo D) {f : D → D} (hinfl : ∀ x : D, x ≤ f x) :
    ∃ x : D, f x = x := by
  classical
  letI : ChainCompletePartialOrder D := chainCompletePartialOrderOfDcpo D hD
  letI : Nonempty D := ⟨⊥⟩
  rcases ChainCompletePartialOrder.nonempty_fixedPoints_of_inflationary
      (α := D) (f := f) hinfl with
    ⟨x, hx⟩
  exact ⟨x, Function.mem_fixedPoints_iff.mp hx⟩

/-- Proposition 2.1.16 support: the chain-supremum side of Proposition 2.1.15
also feeds directly into Bourbaki-Witt for progressive endomaps. -/
theorem chain_sups_inflationary_endomap_has_fixed_point
    {D : Type u} [PartialOrder D] [OrderBot D]
    (hChains : HasChainSups D) {f : D → D} (hinfl : ∀ x : D, x ≤ f x) :
    ∃ x : D, f x = x := by
  classical
  letI : ChainCompletePartialOrder D := chainCompletePartialOrderOfChainSups D hChains
  letI : Nonempty D := ⟨⊥⟩
  rcases ChainCompletePartialOrder.nonempty_fixedPoints_of_inflationary
      (α := D) (f := f) hinfl with
    ⟨x, hx⟩
  exact ⟨x, Function.mem_fixedPoints_iff.mp hx⟩

/-- Proposition 2.1.16, external theorem (Markowsky [Mar76], with the
Pataraia-style proof route isolated above): a pointed poset is a dcpo iff every
monotone self-map has a least fixed point.  This is imported as an explicitly
documented external assumption. -/
axiom prop_2_1_16_pointed_dcpo_iff_lfp
    {D : Type u} [PartialOrder D] [OrderBot D] :
    IsDcpo D ↔ HasLeastFixedPoints D

/-- Proposition 2.1.18: continuous function spaces are dcpos with pointwise
directed suprema. -/
theorem prop_2_1_18_continuous_function_space_dcpo
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) :
    IsDcpo (ScottContFun D E) := by
  intro F hF
  let evalSet (x : D) : Set E := {y | ∃ f ∈ F, y = f x}
  have hEvalDirected : ∀ x : D, DirectedSet (evalSet x) := by
    intro x
    constructor
    · rcases hF.1 with ⟨f, hf⟩
      exact ⟨f x, ⟨f, hf, rfl⟩⟩
    · intro y hy z hz
      rcases hy with ⟨f, hf, rfl⟩
      rcases hz with ⟨g, hg, rfl⟩
      rcases hF.2 hf hg with ⟨k, hk, hfk, hgk⟩
      exact ⟨k x, ⟨k, hk, rfl⟩, hfk x, hgk x⟩
  let gfun : D → E := fun x => Classical.choose (hE (evalSet x) (hEvalDirected x))
  have hgfunSup : ∀ x : D, IsSup (evalSet x) (gfun x) := by
    intro x
    exact Classical.choose_spec (hE (evalSet x) (hEvalDirected x))
  have hgmono : Monotone gfun := by
    intro x y hxy
    exact (hgfunSup x).2 (gfun y) (by
      intro z hz
      rcases hz with ⟨f, hf, rfl⟩
      exact le_trans (f.continuous.1 hxy) ((hgfunSup y).1 ⟨f, hf, rfl⟩))
  have hgcontinuous : ScottContinuous gfun := by
    constructor
    · exact hgmono
    · intro A x hA hx
      constructor
      · intro y hy
        rcases hy with ⟨a, ha, rfl⟩
        exact hgmono (hx.1 ha)
      · intro z hz
        exact (hgfunSup x).2 z (by
          intro y hy
          rcases hy with ⟨f, hf, rfl⟩
          have hfx : IsSup (f.toFun '' A) (f x) := f.continuous.2 hA hx
          exact hfx.2 z (by
            intro w hw
            rcases hw with ⟨a, ha, rfl⟩
            exact le_trans ((hgfunSup a).1 ⟨f, hf, rfl⟩) (hz ⟨a, ha, rfl⟩)))
  let g : ScottContFun D E := { toFun := gfun, continuous := hgcontinuous }
  refine ⟨g, ?_⟩
  constructor
  · intro f hf x
    exact (hgfunSup x).1 ⟨f, hf, rfl⟩
  · intro u hu x
    exact (hgfunSup x).2 (u x) (by
      intro y hy
      rcases hy with ⟨f, hf, rfl⟩
      exact hu hf x)

/-- Directed suprema in the Scott-continuous function space are pointwise. -/
theorem scottContFun_directed_sup_apply
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) {F : Set (ScottContFun D E)} {s : ScottContFun D E}
    (hF : DirectedSet F) (hs : IsSup F s) (x : D) :
    IsSup ((fun f : ScottContFun D E => f x) '' F) (s x) := by
  let evalSet (x : D) : Set E := {y | ∃ f ∈ F, y = f x}
  have hEvalDirected : ∀ x : D, DirectedSet (evalSet x) := by
    intro x
    constructor
    · rcases hF.1 with ⟨f, hf⟩
      exact ⟨f x, ⟨f, hf, rfl⟩⟩
    · intro y hy z hz
      rcases hy with ⟨f, hf, rfl⟩
      rcases hz with ⟨g, hg, rfl⟩
      rcases hF.2 hf hg with ⟨k, hk, hfk, hgk⟩
      exact ⟨k x, ⟨k, hk, rfl⟩, hfk x, hgk x⟩
  let gfun : D → E := fun x => Classical.choose (hE (evalSet x) (hEvalDirected x))
  have hgfunSup : ∀ x : D, IsSup (evalSet x) (gfun x) := by
    intro x
    exact Classical.choose_spec (hE (evalSet x) (hEvalDirected x))
  have hgmono : Monotone gfun := by
    intro x y hxy
    exact (hgfunSup x).2 (gfun y) (by
      intro z hz
      rcases hz with ⟨f, hf, rfl⟩
      exact le_trans (f.continuous.1 hxy) ((hgfunSup y).1 ⟨f, hf, rfl⟩))
  have hgcontinuous : ScottContinuous gfun := by
    constructor
    · exact hgmono
    · intro A a hA ha
      constructor
      · intro y hy
        rcases hy with ⟨b, hb, rfl⟩
        exact hgmono (ha.1 hb)
      · intro z hz
        exact (hgfunSup a).2 z (by
          intro y hy
          rcases hy with ⟨f, hf, rfl⟩
          have hfa : IsSup (f.toFun '' A) (f a) := f.continuous.2 hA ha
          exact hfa.2 z (by
            intro w hw
            rcases hw with ⟨b, hb, rfl⟩
            exact le_trans ((hgfunSup b).1 ⟨f, hf, rfl⟩) (hz ⟨b, hb, rfl⟩)))
  let g : ScottContFun D E := { toFun := gfun, continuous := hgcontinuous }
  have hg_sup : IsSup F g := by
    constructor
    · intro f hf x
      exact (hgfunSup x).1 ⟨f, hf, rfl⟩
    · intro u hu x
      exact (hgfunSup x).2 (u x) (by
        intro y hy
        rcases hy with ⟨f, hf, rfl⟩
        exact hu hf x)
  constructor
  · intro y hy
    rcases hy with ⟨f, hf, rfl⟩
    exact hs.1 hf x
  · intro y hy
    exact le_trans (hs.2 g hg_sup.1 x) ((hgfunSup x).2 y (by
      intro z hz
      rcases hz with ⟨f, hf, rfl⟩
      exact hy ⟨f, hf, rfl⟩))

variable {D : Type u} [PartialOrder D] [OrderBot D]

/-- A chosen supremum in a dcpo. -/
noncomputable def dcpoSup (hD : IsDcpo D) (A : Set D) (hA : DirectedSet A) : D :=
  Classical.choose (hD A hA)

omit [OrderBot D] in
theorem dcpoSup_isSup (hD : IsDcpo D) (A : Set D) (hA : DirectedSet A) :
    IsSup A (dcpoSup hD A hA) :=
  Classical.choose_spec (hD A hA)

/-- Theorem 2.1.19: the Kleene least fixed point chosen from the dcpo structure. -/
noncomputable def chosenLeastFix (hD : IsDcpo D) (f : ScottContFun D D) : D :=
  dcpoSup hD (iterSet f) (iterSet_directed f.continuous.1)

/-- Proposition 2.1.16 / Theorem 2.1.19 support: on a pointed dcpo,
Scott-continuous self maps have least fixed points by the Kleene construction.
The stronger arbitrary-monotone fixed-point equivalence is handled by the
documented external Proposition 2.1.16 proof-debt theorem above. -/
theorem dcpo_scottContinuous_endomap_has_least_fixed_point
    (hD : IsDcpo D) {f : D → D} (hf : ScottContinuous f) :
    ∃ x : D, f x = x ∧ ∀ y : D, f y = y → x ≤ y := by
  let l : D := dcpoSup hD (iterSet f) (iterSet_directed hf.1)
  have hl : IsSup (iterSet f) l :=
    dcpoSup_isSup hD (iterSet f) (iterSet_directed hf.1)
  exact ⟨l, theorem_2_1_19_1 hf hl⟩

/-- The chosen least-fixed-point assignment is monotone in the pointwise function
order. -/
theorem chosenLeastFix_monotone (hD : IsDcpo D) :
    Monotone (fun f : ScottContFun D D => chosenLeastFix hD f) := by
  intro f g hfg
  let lg : D := chosenLeastFix hD g
  have hsupf : IsSup (iterSet f) (chosenLeastFix hD f) :=
    dcpoSup_isSup hD (iterSet f) (iterSet_directed f.continuous.1)
  have hsupg : IsSup (iterSet g) lg :=
    dcpoSup_isSup hD (iterSet g) (iterSet_directed g.continuous.1)
  have hfixg : g lg = lg := (theorem_2_1_19_1 g.continuous hsupg).1
  refine hsupf.2 lg ?_
  intro x hx
  rcases hx with ⟨n, rfl⟩
  induction n with
  | zero =>
      exact bot_le
  | succ n ih =>
      calc
        botIter f (n + 1) = f (botIter f n) := rfl
        _ ≤ f lg := f.continuous.1 ih
        _ ≤ g lg := hfg lg
        _ = lg := hfixg

/-- Each finite Kleene iterate is monotone as a function of the endomap. -/
theorem botIter_function_monotone (n : Nat) :
    Monotone (fun f : ScottContFun D D => botIter f n) := by
  intro f g hfg
  induction n with
  | zero =>
      exact le_rfl
  | succ n ih =>
      calc
        botIter f (n + 1) = f (botIter f n) := rfl
        _ ≤ f (botIter g n) := f.continuous.1 ih
        _ ≤ g (botIter g n) := hfg (botIter g n)

/-- Finite Kleene iterates preserve directed suprema in the function-space
argument. -/
theorem botIter_preserves_directed_sups (hD : IsDcpo D)
    {A : Set (ScottContFun D D)} {s : ScottContFun D D}
    (hA : DirectedSet A) (hs : IsSup A s) :
    ∀ n : Nat,
      IsSup ((fun f : ScottContFun D D => botIter f n) '' A) (botIter s n) := by
  intro n
  induction n with
  | zero =>
      constructor
      · intro x hx
        rcases hx with ⟨_f, _hf, rfl⟩
        exact le_rfl
      · intro y _hy
        exact bot_le
  | succ n ih =>
      have hIterMono : Monotone (fun f : ScottContFun D D => botIter f n) :=
        botIter_function_monotone n
      have hIterDirected :
          DirectedSet ((fun f : ScottContFun D D => botIter f n) '' A) :=
        DirectedSet.image hIterMono hA
      have hs_image_sup :
          IsSup (s '' ((fun f : ScottContFun D D => botIter f n) '' A))
            (s (botIter s n)) :=
        s.continuous.2 hIterDirected ih
      constructor
      · intro x hx
        rcases hx with ⟨f, hfA, rfl⟩
        calc
          botIter f (n + 1) = f (botIter f n) := rfl
          _ ≤ s (botIter f n) := hs.1 hfA (botIter f n)
          _ ≤ s (botIter s n) := s.continuous.1 (ih.1 ⟨f, hfA, rfl⟩)
      · intro y hy
        exact hs_image_sup.2 y (by
          intro z hz
          rcases hz with ⟨x, hx, rfl⟩
          rcases hx with ⟨f, hfA, rfl⟩
          have hEvalSup :
              IsSup ((fun g : ScottContFun D D => g (botIter f n)) '' A)
                (s (botIter f n)) :=
            scottContFun_directed_sup_apply hD hA hs (botIter f n)
          exact hEvalSup.2 y (by
            intro w hw
            rcases hw with ⟨g, hgA, rfl⟩
            rcases hA.2 hfA hgA with ⟨k, hkA, hfk, hgk⟩
            have hf_iter_k : botIter f n ≤ botIter k n := hIterMono hfk
            calc
              g (botIter f n) ≤ k (botIter f n) := hgk (botIter f n)
              _ ≤ k (botIter k n) := k.continuous.1 hf_iter_k
              _ = botIter k (n + 1) := rfl
              _ ≤ y := hy ⟨k, hkA, rfl⟩))

/-- Theorem 2.1.19(2): the least-fixed-point assignment is continuous. -/
theorem theorem_2_1_19_2_fix_assignment_continuous
    (hD : IsDcpo D) :
    ScottContinuous (fun f : ScottContFun D D => chosenLeastFix hD f) := by
  constructor
  · exact chosenLeastFix_monotone hD
  · intro A s hA hs
    constructor
    · intro x hx
      rcases hx with ⟨f, hfA, rfl⟩
      exact chosenLeastFix_monotone hD (hs.1 hfA)
    · intro y hy
      have hsup_s : IsSup (iterSet s) (chosenLeastFix hD s) :=
        dcpoSup_isSup hD (iterSet s) (iterSet_directed s.continuous.1)
      refine hsup_s.2 y ?_
      intro x hx
      rcases hx with ⟨n, rfl⟩
      have hiter_sup :
          IsSup ((fun f : ScottContFun D D => botIter f n) '' A) (botIter s n) :=
        botIter_preserves_directed_sups hD hA hs n
      exact hiter_sup.2 y (by
        intro z hz
        rcases hz with ⟨f, hfA, rfl⟩
        have hsup_f : IsSup (iterSet f) (chosenLeastFix hD f) :=
          dcpoSup_isSup hD (iterSet f) (iterSet_directed f.continuous.1)
        exact le_trans (hsup_f.1 ⟨n, rfl⟩) (hy ⟨f, hfA, rfl⟩))

/-- Lemma 2.1.21: strict commuting squares preserve least fixed points. -/
theorem lemma_2_1_21_fix_invariance
    {E : Type v} [PartialOrder E] [OrderBot E]
    (hD : IsDcpo D) (hE : IsDcpo E)
    (f : ScottContFun D D) (g : ScottContFun E E) (h : ScottContFun D E)
    (hstrict : h ⊥ = ⊥)
    (hcomm : ∀ x : D, h (f x) = g (h x)) :
    chosenLeastFix hE g = h (chosenLeastFix hD f) := by
  let lf : D := chosenLeastFix hD f
  let lg : E := chosenLeastFix hE g
  have hsupf : IsSup (iterSet f) lf :=
    dcpoSup_isSup hD (iterSet f) (iterSet_directed f.continuous.1)
  have hdirf : DirectedSet (iterSet f) := iterSet_directed f.continuous.1
  have hsupImage : IsSup (h '' iterSet f) (h lf) :=
    h.continuous.2 hdirf hsupf
  have hiter : ∀ n : Nat, h (botIter f n) = botIter g n := by
    intro n
    induction n with
    | zero =>
        exact hstrict
    | succ n ih =>
        calc
          h (botIter f (n + 1)) = h (f (botIter f n)) := rfl
          _ = g (h (botIter f n)) := hcomm (botIter f n)
          _ = g (botIter g n) := by rw [ih]
          _ = botIter g (n + 1) := rfl
  have himage : h '' iterSet f = iterSet g := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, hx, rfl⟩
      rcases hx with ⟨n, rfl⟩
      exact ⟨n, (hiter n).symm⟩
    · intro hy
      rcases hy with ⟨n, rfl⟩
      exact ⟨botIter f n, ⟨n, rfl⟩, hiter n⟩
  have hsupg_from_h : IsSup (iterSet g) (h lf) := by
    simpa [himage] using hsupImage
  have hsupg : IsSup (iterSet g) lg :=
    dcpoSup_isSup hE (iterSet g) (iterSet_directed g.continuous.1)
  exact IsSup.unique hsupg hsupg_from_h

end NumberedCoverageOrder

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

/-- Proposition 2.2.14: ω-continuous maps preserve ω-chain suprema. -/
def OmegaContinuousMap {β : Type v} [Preorder β] (f : α → β) : Prop :=
  Monotone f ∧
    ∀ ⦃c : Nat → α⦄ ⦃s : α⦄,
      Monotone c → IsSup (Set.range c) s → IsSup (f '' Set.range c) (f s)

/-- Proposition 2.2.14(1): every continuous ω-ccpo is a continuous dcpo. -/
theorem prop_2_2_14_1_continuous_omega_ccpo_dcpo
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

/-- Proposition 2.2.14(2): every algebraic ω-ccpo is an algebraic dcpo. -/
theorem prop_2_2_14_2_algebraic_omega_ccpo_dcpo
    (hω : IsOmegaCcpo α) (halg : IsOmegaAlgebraicDomain α) :
    IsDcpo α ∧ IsAlgebraicDomain α := by
  exact ⟨prop_2_2_14_1_continuous_omega_ccpo_dcpo hω
    ⟨CompactSet, halg.1, halg.2⟩, halg.2⟩

/-- Proposition 2.2.14(3): ω-continuous maps between continuous ω-ccpos are
Scott-continuous. -/
theorem prop_2_2_14_3_omega_continuous_maps_are_continuous
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

section AbstractBases

/-- Definition 2.2.20: abstract bases. -/
structure AbstractBasis where
  carrier : Type u
  rel : carrier → carrier → Prop
  trans : ∀ ⦃x y z : carrier⦄, rel x y → rel y z → rel x z
  interpolation :
    ∀ x : carrier, ∀ M : Set carrier, M.Finite →
      (∀ m ∈ M, rel m x) →
        ∃ y : carrier, (∀ m ∈ M, rel m y) ∧ rel y x

namespace AbstractBasis

/-- Definition 2.2.20 / Proposition 2.2.25 bridge: a concrete basis of a
continuous domain carries an abstract-basis structure via the way-below
relation. -/
noncomputable def ofConcreteBasis
    {α : Type u} [Preorder α] (Basis : Set α) (hBasis : IsBasis Basis) :
    AbstractBasis.{u} where
  carrier := Basis
  rel x y := (x : α) ≪ (y : α)
  trans := by
    intro x y z hxy hyz
    exact prop_2_2_2_2 le_rfl hxy (prop_2_2_2_1 hyz)
  interpolation := by
    intro x M hM hMx
    let Mval : Set α := Subtype.val '' M
    have hMvalFin : Mval.Finite := hM.image Subtype.val
    have hMvalx : ∀ m ∈ Mval, m ≪ (x : α) := by
      intro m hm
      rcases hm with ⟨b, hbM, rfl⟩
      exact hMx b hbM
    rcases lemma_2_2_15_interpolation_basis hBasis hMvalFin hMvalx with
      ⟨y, hyBasis, hMy, hyx⟩
    refine ⟨⟨y, hyBasis⟩, ?_, hyx⟩
    intro m hm
    exact hMy (m : α) ⟨m, hm, rfl⟩

variable (B : AbstractBasis.{u})

/-- Lower sets in an abstract basis. -/
def IsLower (A : Set B.carrier) : Prop :=
  ∀ ⦃x y : B.carrier⦄, y ∈ A → B.rel x y → x ∈ A

/-- Directed, or round-directed, sets in an abstract basis. -/
def IsDirected (A : Set B.carrier) : Prop :=
  A.Nonempty ∧
    ∀ ⦃x : B.carrier⦄, x ∈ A → ∀ ⦃y : B.carrier⦄, y ∈ A →
      ∃ z ∈ A, B.rel x z ∧ B.rel y z

/-- Definition 2.2.21: ideals in an abstract basis. -/
def IsIdeal (A : Set B.carrier) : Prop :=
  B.IsLower A ∧ B.IsDirected A

/-- Definition 2.2.21: the ideal completion of an abstract basis. -/
def Ideal : Type u :=
  {A : Set B.carrier // B.IsIdeal A}

instance : Preorder B.Ideal where
  le A C := A.1 ⊆ C.1
  le_refl A := by intro x hx; exact hx
  le_trans A C D hAC hCD := by intro x hx; exact hCD (hAC hx)

/-- Definition 2.2.21: the principal ideal map `i : B → Idl(B)`. -/
def principalIdeal (x : B.carrier) : B.Ideal where
  val := {y : B.carrier | B.rel y x}
  property := by
    constructor
    · intro a b hb hab
      exact B.trans hab hb
    · constructor
      · rcases B.interpolation x (∅ : Set B.carrier) (by simp) (by
          intro y hy
          cases hy) with ⟨y, _hyM, hyx⟩
        exact ⟨y, hyx⟩
      · intro a ha b hb
        rcases B.interpolation x ({a, b} : Set B.carrier)
            (by simpa using (Set.finite_singleton b).insert a) (by
              intro y hy
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
              rcases hy with rfl | rfl
              · exact ha
              · exact hb) with
          ⟨z, hzM, hzx⟩
        exact ⟨z, hzx, hzM a (by simp), hzM b (by simp)⟩

/-- Directed unions of ideals are ideals. -/
theorem directedUnionIdeal {A : Set B.Ideal} (hA : DirectedSet A) :
    B.IsIdeal {x : B.carrier | ∃ I ∈ A, x ∈ I.1} := by
  constructor
  · intro x y hy hxy
    rcases hy with ⟨I, hI, hyI⟩
    exact ⟨I, hI, I.property.1 hyI hxy⟩
  · constructor
    · rcases hA.1 with ⟨I, hI⟩
      rcases I.property.2.1 with ⟨x, hxI⟩
      exact ⟨x, ⟨I, hI, hxI⟩⟩
    · intro x hx y hy
      rcases hx with ⟨I, hI, hxI⟩
      rcases hy with ⟨J, hJ, hyJ⟩
      rcases hA.2 hI hJ with ⟨K, hK, hIK, hJK⟩
      have hxK : x ∈ K.1 := hIK hxI
      have hyK : y ∈ K.1 := hJK hyJ
      rcases K.property.2.2 hxK hyK with ⟨z, hzK, hxz, hyz⟩
      exact ⟨z, ⟨K, hK, hzK⟩, hxz, hyz⟩

/-- Proposition 2.2.22(1): ideal completions are dcpos. -/
theorem prop_2_2_22_1_ideal_completion_dcpo :
    IsDcpo B.Ideal := by
  intro A hA
  let Uset : Set B.carrier := {x | ∃ I ∈ A, x ∈ I.1}
  have hUideal : B.IsIdeal Uset := B.directedUnionIdeal hA
  let U : B.Ideal := ⟨Uset, hUideal⟩
  refine ⟨U, ?_⟩
  constructor
  · intro I hI x hxI
    exact ⟨I, hI, hxI⟩
  · intro Y hY x hxU
    rcases hxU with ⟨I, hI, hxI⟩
    exact hY hI hxI

/-- Proposition 2.2.22(2): way-below in the ideal completion. -/
theorem prop_2_2_22_2_ideal_wayBelow {A A' : B.Ideal} :
    A ≪ A' ↔ ∃ x ∈ A'.1, A.1 ⊆ (B.principalIdeal x).1 := by
  constructor
  · intro hAA'
    let P : Set B.Ideal := {I | ∃ x ∈ A'.1, I = B.principalIdeal x}
    have hPdir : DirectedSet P := by
      constructor
      · rcases A'.property.2.1 with ⟨x, hxA'⟩
        exact ⟨B.principalIdeal x, ⟨x, hxA', rfl⟩⟩
      · intro I hI J hJ
        rcases hI with ⟨x, hxA', rfl⟩
        rcases hJ with ⟨y, hyA', rfl⟩
        rcases A'.property.2.2 hxA' hyA' with ⟨z, hzA', hxz, hyz⟩
        refine ⟨B.principalIdeal z, ⟨z, hzA', rfl⟩, ?_, ?_⟩
        · intro w hw
          exact B.trans hw hxz
        · intro w hw
          exact B.trans hw hyz
    have hPsup : IsSup P A' := by
      constructor
      · intro I hI y hyI
        rcases hI with ⟨x, hxA', rfl⟩
        exact A'.property.1 hxA' hyI
      · intro Y hY y hyA'
        rcases A'.property.2.2 hyA' hyA' with ⟨z, hzA', hyz, _⟩
        exact hY ⟨z, hzA', rfl⟩ hyz
    rcases hAA' hPdir hPsup le_rfl with ⟨I, hI, hAI⟩
    rcases hI with ⟨x, hxA', rfl⟩
    exact ⟨x, hxA', hAI⟩
  · rintro ⟨x, hxA', hAx⟩
    intro F s hF hs hA's
    let Uset : Set B.carrier := {y | ∃ I ∈ F, y ∈ I.1}
    let U : B.Ideal := ⟨Uset, B.directedUnionIdeal hF⟩
    have hUupper : IsUpperBound F U := by
      intro I hI y hyI
      exact ⟨I, hI, hyI⟩
    have hsU : s ≤ U := hs.2 U hUupper
    have hxU : x ∈ U.1 := hsU (hA's hxA')
    rcases hxU with ⟨I, hI, hxI⟩
    refine ⟨I, hI, ?_⟩
    intro y hyA
    exact I.property.1 hxI (hAx hyA)

/-- Principal ideals form a basis for the ideal completion. -/
theorem principalIdealBasisRaw :
    IsBasisRaw (Set.range B.principalIdeal) := by
  intro A
  let S : Set B.Ideal := {I | ∃ x ∈ A.1, I = B.principalIdeal x}
  have hSsub : S ⊆ Approximants (Set.range B.principalIdeal) A := by
    intro I hI
    rcases hI with ⟨x, hxA, rfl⟩
    constructor
    · exact ⟨x, rfl⟩
    · apply (B.prop_2_2_22_2_ideal_wayBelow
        (A := B.principalIdeal x) (A' := A)).2
      rcases A.property.2.2 hxA hxA with ⟨y, hyA, hxy, _⟩
      exact ⟨y, hyA, by
        intro z hz
        exact B.trans hz hxy⟩
  have hSdir : DirectedSet S := by
    constructor
    · rcases A.property.2.1 with ⟨x, hxA⟩
      exact ⟨B.principalIdeal x, ⟨x, hxA, rfl⟩⟩
    · intro I hI J hJ
      rcases hI with ⟨x, hxA, rfl⟩
      rcases hJ with ⟨y, hyA, rfl⟩
      rcases A.property.2.2 hxA hyA with ⟨z, hzA, hxz, hyz⟩
      refine ⟨B.principalIdeal z, ⟨z, hzA, rfl⟩, ?_, ?_⟩
      · intro w hw
        exact B.trans hw hxz
      · intro w hw
        exact B.trans hw hyz
  have hSsup : IsSup S A := by
    constructor
    · intro I hI y hyI
      rcases hI with ⟨x, hxA, rfl⟩
      exact A.property.1 hxA hyI
    · intro Y hY y hyA
      rcases A.property.2.2 hyA hyA with ⟨z, hzA, hyz, _⟩
      exact hY ⟨z, hzA, rfl⟩ hyz
  exact ⟨S, hSsub, hSdir, hSsup⟩

/-- Proposition 2.2.22(3): `i(B)` is a basis for the ideal completion. -/
theorem prop_2_2_22_3_ideal_completion_continuous :
    IsContinuousDomain B.Ideal := by
  exact ⟨Set.range B.principalIdeal, B.principalIdealBasisRaw⟩

/-- Proposition 2.2.25 support: the ideal completion of the abstract basis
extracted from a concrete basis is a continuous domain. -/
theorem ofConcreteBasis_ideal_completion_continuous
    {α : Type u} [Preorder α] {Basis : Set α} (hBasis : IsBasis Basis) :
    IsContinuousDomain ((ofConcreteBasis Basis hBasis).Ideal) := by
  exact (ofConcreteBasis Basis hBasis).prop_2_2_22_3_ideal_completion_continuous

/-- Proposition 2.2.22(4): reflexive abstract bases have algebraic completions. -/
theorem prop_2_2_22_4_reflexive_ideal_completion_algebraic
    (hrefl : ∀ x : B.carrier, B.rel x x) :
    IsAlgebraicDomain B.Ideal := by
  exact prop_2_2_4_3 B.principalIdealBasisRaw (by
    intro I hI
    rcases hI with ⟨x, rfl⟩
    apply (B.prop_2_2_22_2_ideal_wayBelow
      (A := B.principalIdeal x) (A' := B.principalIdeal x)).2
    exact ⟨x, hrefl x, by intro y hy; exact hy⟩)

/-- Proposition 2.2.22(5): for posets, the basis is isomorphic to the compact
elements of its ideal completion. -/
theorem prop_2_2_22_5_poset_compacts
    (hrefl : ∀ x : B.carrier, B.rel x x)
    (hantisymm : ∀ ⦃x y : B.carrier⦄, B.rel x y → B.rel y x → x = y) :
    Nonempty (B.carrier ≃ {I : B.Ideal // Compact I}) := by
  classical
  have hcompactPrincipal : ∀ x : B.carrier, Compact (B.principalIdeal x) := by
    intro x
    apply (B.prop_2_2_22_2_ideal_wayBelow
      (A := B.principalIdeal x) (A' := B.principalIdeal x)).2
    exact ⟨x, hrefl x, by intro y hy; exact hy⟩
  have hrepr : ∀ K : {I : B.Ideal // Compact I},
      ∃ x : B.carrier, K.1 = B.principalIdeal x := by
    intro K
    rcases (B.prop_2_2_22_2_ideal_wayBelow
        (A := K.1) (A' := K.1)).1 K.2 with
      ⟨x, hxK, hKx⟩
    have hxsub : (B.principalIdeal x).1 ⊆ K.1.1 := by
      intro y hy
      exact K.1.property.1 hxK hy
    have hset : K.1.1 = (B.principalIdeal x).1 :=
      Set.Subset.antisymm hKx hxsub
    exact ⟨x, Subtype.ext hset⟩
  refine ⟨{
    toFun := fun x => ⟨B.principalIdeal x, hcompactPrincipal x⟩
    invFun := fun K => Classical.choose (hrepr K)
    left_inv := ?_
    right_inv := ?_
  }⟩
  · intro x
    let K : {I : B.Ideal // Compact I} := ⟨B.principalIdeal x, hcompactPrincipal x⟩
    let y : B.carrier := Classical.choose (hrepr K)
    have hK : K.1 = B.principalIdeal y := by
      simpa [y] using Classical.choose_spec (hrepr K)
    have hxy : B.rel x y := by
      have hx : x ∈ K.1.1 := hrefl x
      rw [hK] at hx
      exact hx
    have hyx : B.rel y x := by
      have hy : y ∈ (B.principalIdeal y).1 := hrefl y
      have hyK : y ∈ K.1.1 := by
        rwa [hK]
      simpa [K] using hyK
    change y = x
    exact (hantisymm hxy hyx).symm
  · intro K
    have hK : K.1 = B.principalIdeal (Classical.choose (hrepr K)) :=
      Classical.choose_spec (hrepr K)
    exact Subtype.ext hK.symm

variable (C : AbstractBasis.{u})

/-- Product of abstract bases. -/
def prod : AbstractBasis.{u} where
  carrier := B.carrier × C.carrier
  rel p q := B.rel p.1 q.1 ∧ C.rel p.2 q.2
  trans := by
    intro x y z hxy hyz
    exact ⟨B.trans hxy.1 hyz.1, C.trans hxy.2 hyz.2⟩
  interpolation := by
    intro x M hM hMx
    let M₁ : Set B.carrier := Prod.fst '' M
    let M₂ : Set C.carrier := Prod.snd '' M
    have hM₁fin : M₁.Finite := hM.image Prod.fst
    have hM₂fin : M₂.Finite := hM.image Prod.snd
    have hM₁x : ∀ m ∈ M₁, B.rel m x.1 := by
      intro m hm
      rcases hm with ⟨p, hpM, rfl⟩
      exact (hMx p hpM).1
    have hM₂x : ∀ m ∈ M₂, C.rel m x.2 := by
      intro m hm
      rcases hm with ⟨p, hpM, rfl⟩
      exact (hMx p hpM).2
    rcases B.interpolation x.1 M₁ hM₁fin hM₁x with ⟨b, hbM, hbx⟩
    rcases C.interpolation x.2 M₂ hM₂fin hM₂x with ⟨c, hcM, hcx⟩
    refine ⟨(b, c), ?_, ⟨hbx, hcx⟩⟩
    intro p hpM
    exact ⟨hbM p.1 ⟨p, hpM, rfl⟩, hcM p.2 ⟨p, hpM, rfl⟩⟩

/-- Proposition 2.2.23: ideal completion preserves products. -/
theorem prop_2_2_23_ideal_completion_product :
    Nonempty ((B.prod C).Ideal ≃ B.Ideal × C.Ideal) := by
  let leftIdeal (I : (B.prod C).Ideal) : B.Ideal := {
    val := {x : B.carrier | ∃ y : C.carrier, (x, y) ∈ I.1}
    property := by
      constructor
      · intro x y hy hxy
        rcases hy with ⟨c, hyc⟩
        rcases I.property.2.2 hyc hyc with ⟨q, hq, hycq, _⟩
        exact ⟨c, I.property.1 hq ⟨B.trans hxy hycq.1, hycq.2⟩⟩
      · constructor
        · rcases I.property.2.1 with ⟨p, hp⟩
          exact ⟨p.1, p.2, hp⟩
        · intro x hx y hy
          rcases hx with ⟨cx, hxI⟩
          rcases hy with ⟨cy, hyI⟩
          rcases I.property.2.2 hxI hyI with ⟨z, hz, hxz, hyz⟩
          exact ⟨z.1, ⟨z.2, hz⟩, hxz.1, hyz.1⟩
  }
  let rightIdeal (I : (B.prod C).Ideal) : C.Ideal := {
    val := {y : C.carrier | ∃ x : B.carrier, (x, y) ∈ I.1}
    property := by
      constructor
      · intro x y hy hxy
        rcases hy with ⟨b, hby⟩
        rcases I.property.2.2 hby hby with ⟨q, hq, hbyq, _⟩
        exact ⟨b, I.property.1 hq ⟨hbyq.1, C.trans hxy hbyq.2⟩⟩
      · constructor
        · rcases I.property.2.1 with ⟨p, hp⟩
          exact ⟨p.2, p.1, hp⟩
        · intro x hx y hy
          rcases hx with ⟨bx, hxI⟩
          rcases hy with ⟨bY, hyI⟩
          rcases I.property.2.2 hxI hyI with ⟨z, hz, hxz, hyz⟩
          exact ⟨z.2, ⟨z.1, hz⟩, hxz.2, hyz.2⟩
  }
  let toPair (I : (B.prod C).Ideal) : B.Ideal × C.Ideal :=
    (leftIdeal I, rightIdeal I)
  let productIdeal : B.Ideal × C.Ideal → (B.prod C).Ideal := fun P => {
    val := {p | p.1 ∈ P.1.1 ∧ p.2 ∈ P.2.1}
    property := by
      constructor
      · intro p q hq hpq
        exact ⟨P.1.property.1 hq.1 hpq.1, P.2.property.1 hq.2 hpq.2⟩
      · constructor
        · rcases P.1.property.2.1 with ⟨x, hx⟩
          rcases P.2.property.2.1 with ⟨y, hy⟩
          exact ⟨(x, y), hx, hy⟩
        · intro p hp q hq
          rcases P.1.property.2.2 hp.1 hq.1 with ⟨x, hx, hpx, hqx⟩
          rcases P.2.property.2.2 hp.2 hq.2 with ⟨y, hy, hpy, hqy⟩
          exact ⟨(x, y), ⟨hx, hy⟩, ⟨hpx, hpy⟩, ⟨hqx, hqy⟩⟩
  }
  refine ⟨{
    toFun := toPair
    invFun := productIdeal
    left_inv := ?_
    right_inv := ?_
  }⟩
  · intro I
    apply Subtype.ext
    ext p
    constructor
    · intro hp
      rcases hp with ⟨hp₁, hp₂⟩
      rcases hp₁ with ⟨y, hpy⟩
      rcases hp₂ with ⟨x, hxp⟩
      rcases I.property.2.2 hpy hxp with ⟨z, hz, hpyz, hxpz⟩
      exact I.property.1 hz ⟨hpyz.1, hxpz.2⟩
    · intro hp
      exact ⟨⟨p.2, hp⟩, ⟨p.1, hp⟩⟩
  · intro P
    cases P with
    | mk I J =>
        apply Prod.ext
        · apply Subtype.ext
          ext x
          constructor
          · intro hx
            rcases hx with ⟨y, hxy⟩
            exact hxy.1
          · intro hx
            rcases J.property.2.1 with ⟨y, hy⟩
            exact ⟨y, hx, hy⟩
        · apply Subtype.ext
          ext y
          constructor
          · intro hy
            rcases hy with ⟨x, hxy⟩
            exact hxy.2
          · intro hy
            rcases I.property.2.1 with ⟨x, hx⟩
            exact ⟨x, hx, hy⟩

/-- Monotone maps from an abstract basis into a preorder. -/
def MonotoneToPreorder {D : Type v} [Preorder D] (f : B.carrier → D) : Prop :=
  ∀ ⦃x y : B.carrier⦄, B.rel x y → f x ≤ f y

/-- Values of a basis map on an ideal, whose directed supremum defines its
canonical extension. -/
def extensionValues {D : Type v} [Preorder D] (f : B.carrier → D)
    (A : B.Ideal) : Set D :=
  {d | ∃ x ∈ A.1, d = f x}

/-- Proposition 2.2.24: the canonical largest extension of a monotone basis map.
The result exposes the supremum formula and the equality on principal ideals
when the abstract-basis relation is reflexive. -/
theorem prop_2_2_24_extension_universal
    {D : Type v} [Preorder D] (hD : IsDcpo D)
    (hDanti : IsAntisymmetricOrder D)
    {f : B.carrier → D} (hf : B.MonotoneToPreorder f) :
    ∃ fhat : B.Ideal → D,
      (∀ A : B.Ideal, IsSup (B.extensionValues f A) (fhat A)) ∧
      ScottContinuous fhat ∧
        (∀ x : B.carrier, fhat (B.principalIdeal x) ≤ f x) ∧
        (∀ g : B.Ideal → D,
          ScottContinuous g →
            (∀ x : B.carrier, g (B.principalIdeal x) ≤ f x) →
              ∀ A : B.Ideal, g A ≤ fhat A) ∧
        ((∀ x : B.carrier, B.rel x x) →
          ∀ x : B.carrier, fhat (B.principalIdeal x) = f x) := by
  have hValueDirected : ∀ A : B.Ideal, DirectedSet (B.extensionValues f A) := by
    intro A
    constructor
    · rcases A.property.2.1 with ⟨x, hx⟩
      exact ⟨f x, ⟨x, hx, rfl⟩⟩
    · intro u hu v hv
      rcases hu with ⟨x, hxA, rfl⟩
      rcases hv with ⟨y, hyA, rfl⟩
      rcases A.property.2.2 hxA hyA with ⟨z, hzA, hxz, hyz⟩
      exact ⟨f z, ⟨z, hzA, rfl⟩, hf hxz, hf hyz⟩
  let fhat : B.Ideal → D := fun A =>
    Classical.choose (hD (B.extensionValues f A) (hValueDirected A))
  have hfhatSup : ∀ A : B.Ideal, IsSup (B.extensionValues f A) (fhat A) := by
    intro A
    exact Classical.choose_spec (hD (B.extensionValues f A) (hValueDirected A))
  refine ⟨fhat, hfhatSup, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro A C hAC
      exact (hfhatSup A).2 (fhat C) (by
        intro d hd
        rcases hd with ⟨x, hxA, rfl⟩
        exact (hfhatSup C).1 ⟨x, hAC hxA, rfl⟩)
    · intro F X hF hsup
      constructor
      · intro d hd
        rcases hd with ⟨A, hAF, rfl⟩
        exact (hfhatSup A).2 (fhat X) (by
          intro e he
          rcases he with ⟨x, hxA, rfl⟩
          exact (hfhatSup X).1 ⟨x, hsup.1 hAF hxA, rfl⟩)
      · intro y hy
        exact (hfhatSup X).2 y (by
          intro d hd
          rcases hd with ⟨x, hxX, rfl⟩
          let U : B.Ideal :=
            ⟨{z : B.carrier | ∃ A ∈ F, z ∈ A.1}, B.directedUnionIdeal hF⟩
          have hUupper : IsUpperBound F U := by
            intro A hAF z hzA
            exact ⟨A, hAF, hzA⟩
          have hXU : X ≤ U := hsup.2 U hUupper
          rcases hXU hxX with ⟨A, hAF, hxA⟩
          exact le_trans ((hfhatSup A).1 ⟨x, hxA, rfl⟩) (hy ⟨A, hAF, rfl⟩))
  · intro x
    exact (hfhatSup (B.principalIdeal x)).2 (f x) (by
      intro d hd
      rcases hd with ⟨y, hyx, rfl⟩
      exact hf hyx)
  · intro g hg hg_principal A
    let P : Set B.Ideal := {I | ∃ x ∈ A.1, I = B.principalIdeal x}
    have hPdir : DirectedSet P := by
      constructor
      · rcases A.property.2.1 with ⟨x, hxA⟩
        exact ⟨B.principalIdeal x, ⟨x, hxA, rfl⟩⟩
      · intro I hI J hJ
        rcases hI with ⟨x, hxA, rfl⟩
        rcases hJ with ⟨y, hyA, rfl⟩
        rcases A.property.2.2 hxA hyA with ⟨z, hzA, hxz, hyz⟩
        refine ⟨B.principalIdeal z, ⟨z, hzA, rfl⟩, ?_, ?_⟩
        · intro w hw
          exact B.trans hw hxz
        · intro w hw
          exact B.trans hw hyz
    have hPsup : IsSup P A := by
      constructor
      · intro I hI y hyI
        rcases hI with ⟨x, hxA, rfl⟩
        exact A.property.1 hxA hyI
      · intro Y hY y hyA
        rcases A.property.2.2 hyA hyA with ⟨z, hzA, hyz, _⟩
        exact hY ⟨z, hzA, rfl⟩ hyz
    have hgSup : IsSup (g '' P) (g A) := hg.2 hPdir hPsup
    exact hgSup.2 (fhat A) (by
      intro d hd
      rcases hd with ⟨I, hI, rfl⟩
      rcases hI with ⟨x, hxA, rfl⟩
      exact le_trans (hg_principal x) ((hfhatSup A).1 ⟨x, hxA, rfl⟩))
  · intro hrefl x
    apply hDanti
    · exact (hfhatSup (B.principalIdeal x)).2 (f x) (by
        intro d hd
        rcases hd with ⟨y, hyx, rfl⟩
        exact hf hyx)
    · exact (hfhatSup (B.principalIdeal x)).1 ⟨x, hrefl x, rfl⟩


structure MonotoneBasisMap (B : AbstractBasis.{u}) (D : Type v) [Preorder D] where
  toFun : B.carrier → D
  monotone : B.MonotoneToPreorder toFun

namespace MonotoneBasisMap

instance {B : AbstractBasis.{u}} {D : Type v} [Preorder D] :
    CoeFun (MonotoneBasisMap B D) (fun _ => B.carrier → D) where
  coe f := f.toFun

instance {B : AbstractBasis.{u}} {D : Type v} [Preorder D] :
    Preorder (MonotoneBasisMap B D) where
  le f g := ∀ x, f x ≤ g x
  le_refl f x := le_rfl
  le_trans f g h hfg hgh x := le_trans (hfg x) (hgh x)

@[ext]
theorem ext {B : AbstractBasis.{u}} {D : Type v} [Preorder D]
    {f g : MonotoneBasisMap B D} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f hf =>
      cases g with
      | mk g hg =>
          have hfg : f = g := funext h
          subst g
          rfl

end MonotoneBasisMap

variable (B : AbstractBasis.{u}) {D : Type v} [Preorder D]

def monotoneMapEvalSet (F : Set (MonotoneBasisMap B D)) (x : B.carrier) : Set D :=
  (fun f : MonotoneBasisMap B D => f x) '' F

theorem monotoneMapEvalSet_directed {F : Set (MonotoneBasisMap B D)}
    (hF : DirectedSet F) (x : B.carrier) :
    DirectedSet (B.monotoneMapEvalSet F x) :=
  DirectedSet.image (f := fun f : MonotoneBasisMap B D => f x)
    (by intro f g hfg; exact hfg x) hF

noncomputable def monotoneMapDirectedSup (hD : IsDcpo D)
    (F : Set (MonotoneBasisMap B D)) (hF : DirectedSet F) :
    MonotoneBasisMap B D where
  toFun x := Classical.choose (hD (B.monotoneMapEvalSet F x)
    (B.monotoneMapEvalSet_directed hF x))
  monotone := by
    intro x y hxy
    let sx := Classical.choose (hD (B.monotoneMapEvalSet F x)
      (B.monotoneMapEvalSet_directed hF x))
    let sy := Classical.choose (hD (B.monotoneMapEvalSet F y)
      (B.monotoneMapEvalSet_directed hF y))
    have hsx := Classical.choose_spec (hD (B.monotoneMapEvalSet F x)
      (B.monotoneMapEvalSet_directed hF x))
    have hsy := Classical.choose_spec (hD (B.monotoneMapEvalSet F y)
      (B.monotoneMapEvalSet_directed hF y))
    exact hsx.2 sy (by
      intro d hd
      rcases hd with ⟨f, hfF, rfl⟩
      exact le_trans (f.monotone hxy) (hsy.1 ⟨f, hfF, rfl⟩))

theorem monotoneMapDirectedSup_value_isSup (hD : IsDcpo D)
    {F : Set (MonotoneBasisMap B D)} (hF : DirectedSet F) (x : B.carrier) :
    IsSup (B.monotoneMapEvalSet F x) (B.monotoneMapDirectedSup hD F hF x) :=
  Classical.choose_spec (hD (B.monotoneMapEvalSet F x)
    (B.monotoneMapEvalSet_directed hF x))

theorem monotoneMapDirectedSup_isSup (hD : IsDcpo D)
    {F : Set (MonotoneBasisMap B D)} (hF : DirectedSet F) :
    IsSup F (B.monotoneMapDirectedSup hD F hF) := by
  constructor
  · intro f hfF x
    exact (B.monotoneMapDirectedSup_value_isSup hD hF x).1 ⟨f, hfF, rfl⟩
  · intro g hg x
    exact (B.monotoneMapDirectedSup_value_isSup hD hF x).2 (g x) (by
      intro d hd
      rcases hd with ⟨f, hfF, rfl⟩
      exact hg hfF x)

noncomputable def canonicalExtension (hD : IsDcpo D)
    (hDanti : IsAntisymmetricOrder D) (f : MonotoneBasisMap B D) :
    B.Ideal → D :=
  Classical.choose (B.prop_2_2_24_extension_universal hD hDanti f.monotone)

theorem canonicalExtension_spec (hD : IsDcpo D)
    (hDanti : IsAntisymmetricOrder D) (f : MonotoneBasisMap B D) :
    ∀ A : B.Ideal, IsSup (B.extensionValues f A) (B.canonicalExtension hD hDanti f A) :=
  (Classical.choose_spec
    (B.prop_2_2_24_extension_universal hD hDanti f.monotone)).1

theorem canonicalExtension_continuous (hD : IsDcpo D)
    (hDanti : IsAntisymmetricOrder D) (f : MonotoneBasisMap B D) :
    ScottContinuous (B.canonicalExtension hD hDanti f) :=
  (Classical.choose_spec
    (B.prop_2_2_24_extension_universal hD hDanti f.monotone)).2.1

noncomputable def extensionOperator (hD : IsDcpo D)
    (hDanti : IsAntisymmetricOrder D) :
    MonotoneBasisMap B D → ScottContFun B.Ideal D := fun f =>
  { toFun := B.canonicalExtension hD hDanti f
    continuous := B.canonicalExtension_continuous hD hDanti f }

theorem extensionOperator_monotone (hD : IsDcpo D)
    (hDanti : IsAntisymmetricOrder D) :
    Monotone (B.extensionOperator hD hDanti) := by
  intro f g hfg A
  exact (B.canonicalExtension_spec hD hDanti f A).2
    (B.canonicalExtension hD hDanti g A) (by
      intro d hd
      rcases hd with ⟨x, hxA, rfl⟩
      exact le_trans (hfg x)
        ((B.canonicalExtension_spec hD hDanti g A).1 ⟨x, hxA, rfl⟩))

theorem extensionOperator_scottContinuous (hD : IsDcpo D)
    (hDanti : IsAntisymmetricOrder D) :
    ScottContinuous (B.extensionOperator hD hDanti) := by
  refine ⟨B.extensionOperator_monotone hD hDanti, ?_⟩
  intro F s hF hs
  let ds := B.monotoneMapDirectedSup hD F hF
  have hds : IsSup F ds := B.monotoneMapDirectedSup_isSup hD hF
  have hdss : ds = s := by
    apply MonotoneBasisMap.ext
    intro x
    apply hDanti
    · exact (hds.2 s hs.1) x
    · exact (hs.2 ds hds.1) x
  constructor
  · intro ef hef
    rcases hef with ⟨f, hfF, rfl⟩
    exact B.extensionOperator_monotone hD hDanti (hs.1 hfF)
  · intro G hG A
    apply (B.canonicalExtension_spec hD hDanti s A).2
    intro d hd
    rcases hd with ⟨x, hxA, rfl⟩
    rw [← hdss]
    exact (B.monotoneMapDirectedSup_value_isSup hD hF x).2 (G A) (by
      intro e he
      rcases he with ⟨f, hfF, rfl⟩
      exact le_trans
        ((B.canonicalExtension_spec hD hDanti f A).1 ⟨x, hxA, rfl⟩)
        (hG ⟨f, hfF, rfl⟩ A))

end AbstractBasis

/-- Continuous-domain objects used for Theorem 2.2.28. -/
structure ContinuousDomainObject where
  carrier : Type u
  preorder : Preorder carrier
  dcpo : @IsDcpo carrier preorder
  antisymmetric : @IsAntisymmetricOrder carrier preorder
  basis : Set carrier
  isBasis : @IsBasisRaw carrier preorder basis

/-- Presentation objects for Theorem 2.2.28: a continuous-domain object together
with the abstract basis that presents it.  This keeps the categorical-equivalence
statement separate from arbitrary bundled continuous domains. -/
structure ContinuousDomainPresentationObject where
  basisObject : AbstractBasis.{u}

/-- Algebraic-domain objects used for Theorem 2.2.29. -/
structure AlgebraicDomainObject where
  carrier : Type u
  preorder : Preorder carrier
  dcpo : @IsDcpo carrier preorder
  antisymmetric : @IsAntisymmetricOrder carrier preorder
  isAlgebraic : @IsAlgebraicDomain carrier preorder

/-- Presentation objects for Theorem 2.2.29: algebraic domains presented by
reflexive abstract bases/preorders. -/
structure AlgebraicDomainPresentationObject where
  basisObject : AbstractBasis.{u}
  reflexive : ∀ x : basisObject.carrier, basisObject.rel x x

namespace AbstractBasis

variable (B : AbstractBasis.{u})

/-- Proposition 2.2.25 support: for a dcpo with a concrete basis, the canonical
ideal-completion presentation can be constructed explicitly. -/
noncomputable def concreteBasisIdealEquiv
    {D : Type u} [PartialOrder D] (hD : IsDcpo D)
    {Basis : Set D} (hBasis : IsBasis Basis) :
    (ofConcreteBasis Basis hBasis).Ideal ≃ D := by
  classical
  let Bc : AbstractBasis.{u} := ofConcreteBasis Basis hBasis
  let val : Bc.carrier → D := by
    dsimp [Bc, ofConcreteBasis]
    exact fun b : Basis => (b : D)
  let carrierSet : Bc.Ideal → Set D := fun I =>
    {x | ∃ b : Bc.carrier, b ∈ I.1 ∧ x = val b}
  have hCarrierDirected : ∀ I : Bc.Ideal, DirectedSet (carrierSet I) := by
    intro I
    constructor
    · rcases I.property.2.1 with ⟨b, hb⟩
      exact ⟨val b, ⟨b, hb, rfl⟩⟩
    · intro x hx y hy
      rcases hx with ⟨b, hbI, rfl⟩
      rcases hy with ⟨c, hcI, rfl⟩
      rcases I.property.2.2 hbI hcI with ⟨z, hzI, hbz, hcz⟩
      have hbzD : val b ≪ val z := by
        dsimp [Bc, ofConcreteBasis, val] at hbz ⊢
        exact hbz
      have hczD : val c ≪ val z := by
        dsimp [Bc, ofConcreteBasis, val] at hcz ⊢
        exact hcz
      exact ⟨val z, ⟨z, hzI, rfl⟩, prop_2_2_2_1 hbzD, prop_2_2_2_1 hczD⟩
  let supIdeal : Bc.Ideal → D := fun I =>
    Classical.choose (hD (carrierSet I) (hCarrierDirected I))
  have hSupIdeal : ∀ I : Bc.Ideal, IsSup (carrierSet I) (supIdeal I) := by
    intro I
    exact Classical.choose_spec (hD (carrierSet I) (hCarrierDirected I))
  let idealOf : D → Bc.Ideal := fun x =>
    ⟨{b : Bc.carrier | val b ≪ x}, ?_⟩
  · refine {
      toFun := supIdeal
      invFun := idealOf
      left_inv := ?_
      right_inv := ?_
    }
    · intro I
      apply Subtype.ext
      ext b
      constructor
      · intro hb
        have hbBelow : val b ≪ supIdeal I := hb
        have hcont : IsContinuousDomain D := ⟨Basis, basis_to_raw hBasis⟩
        rcases cor_2_2_16_wayBelow_directed_sup hcont
            (hCarrierDirected I) (hSupIdeal I) hbBelow with
          ⟨d, hdCarrier, hbd⟩
        rcases hdCarrier with ⟨c, hcI, rfl⟩
        have hbcRel : Bc.rel b c := by
          dsimp [Bc, ofConcreteBasis, val] at hbd ⊢
          exact hbd
        exact I.property.1 hcI hbcRel
      · intro hbI
        rcases I.property.2.2 hbI hbI with ⟨c, hcI, hbc, _⟩
        have hbcD : val b ≪ val c := by
          dsimp [Bc, ofConcreteBasis, val] at hbc ⊢
          exact hbc
        exact prop_2_2_2_2 le_rfl hbcD ((hSupIdeal I).1 ⟨c, hcI, rfl⟩)
    · intro x
      apply IsSup.unique (hSupIdeal (idealOf x))
      constructor
      · intro y hy
        rcases hy with ⟨b, hb, rfl⟩
        exact prop_2_2_2_1 hb
      · intro y hy
        exact (hBasis x).2.2 y (by
          intro b hb
          exact hy ⟨⟨b, hb.1⟩, hb.2, rfl⟩)
  · constructor
    · intro b c hc hbc
      have hbcD : val b ≪ val c := by
        dsimp [Bc, ofConcreteBasis, val] at hbc ⊢
        exact hbc
      exact prop_2_2_2_2 le_rfl hbcD (prop_2_2_2_1 hc)
    · constructor
      · rcases (hBasis x).1.1 with ⟨b, hb⟩
        exact ⟨⟨b, hb.1⟩, hb.2⟩
      · intro b hb c hc
        let M : Set D := {val b, val c}
        have hMfin : M.Finite := by
          simpa [M] using (Set.finite_singleton (val c)).insert (val b)
        have hMx : ∀ m ∈ M, m ≪ x := by
          intro m hm
          simp only [M, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
          rcases hm with rfl | rfl
          · exact hb
          · exact hc
        rcases lemma_2_2_15_interpolation_basis hBasis hMfin hMx with
          ⟨z, hzBasis, hMz, hzx⟩
        refine ⟨⟨z, hzBasis⟩, hzx, ?_, ?_⟩
        · have hbzD : val b ≪ z := hMz (val b) (by simp [M])
          dsimp [Bc, ofConcreteBasis, val] at hbzD ⊢
          exact hbzD
        · have hczD : val c ≪ z := hMz (val c) (by simp [M])
          dsimp [Bc, ofConcreteBasis, val] at hczD ⊢
          exact hczD

/-- Proposition 2.2.25, concrete-basis form: a partial-order dcpo with a concrete
basis is equivalent to the ideal completion of the induced abstract basis. -/
theorem prop_2_2_25_domain_iso_ideal_completion
    {D : Type u} [PartialOrder D] (hD : IsDcpo D)
    {Basis : Set D} (hBasis : IsBasis Basis) :
    Nonempty ((ofConcreteBasis Basis hBasis).Ideal ≃ D) := by
  exact ⟨concreteBasisIdealEquiv hD hBasis⟩

/-- Corollary 2.2.26: continuous maps from a continuous domain are determined by
their values on a basis. -/
theorem cor_2_2_26_continuous_map_determined_by_basis
    {D : Type u} {E : Type v} [Preorder D] [PartialOrder E] {Basis : Set D}
    (hB : IsBasis Basis) {f g : D → E}
    (hf : ScottContinuous f) (hg : ScottContinuous g)
    (hfg : ∀ b ∈ Basis, f b = g b) :
    f = g := by
  funext x
  apply le_antisymm
  · have hfsup : IsSup (f '' Approximants Basis x) (f x) :=
      hf.2 (hB x).1 (hB x).2
    exact hfsup.2 (g x) (by
      intro y hy
      rcases hy with ⟨b, hb, rfl⟩
      calc
        f b = g b := hfg b hb.1
        _ ≤ g x := hg.1 (prop_2_2_2_1 hb.2))
  · have hgsup : IsSup (g '' Approximants Basis x) (g x) :=
      hg.2 (hB x).1 (hB x).2
    exact hgsup.2 (f x) (by
      intro y hy
      rcases hy with ⟨b, hb, rfl⟩
      calc
        g b = f b := (hfg b hb.1).symm
        _ ≤ f x := hf.1 (prop_2_2_2_1 hb.2))

/-- Definition 2.2.27: approximable relations between abstract bases. -/
structure ApproximableRelation (C : AbstractBasis.{u}) where
  rel : B.carrier → C.carrier → Prop
  lower_right :
    ∀ ⦃x : B.carrier⦄ ⦃y y' : C.carrier⦄,
      rel x y → C.rel y' y → rel x y'
  finite_interpolation :
    ∀ x : B.carrier, ∀ M : Set C.carrier, M.Finite →
      (∀ y ∈ M, rel x y) →
        ∃ z : C.carrier, rel x z ∧ ∀ y ∈ M, C.rel y z
  upper_left :
    ∀ ⦃x x' : B.carrier⦄ ⦃y : C.carrier⦄,
      B.rel x x' → rel x y → rel x' y
  rounded :
    ∀ ⦃x : B.carrier⦄ ⦃y : C.carrier⦄,
      rel x y → ∃ z : B.carrier, B.rel z x ∧ rel z y

/-- Identity approximable relation: `x` relates to each approximation below
it. -/
def approximableId (B : AbstractBasis.{u}) : B.ApproximableRelation B where
  rel x y := B.rel y x
  lower_right := by
    intro x y y' hxy hy'y
    exact B.trans hy'y hxy
  finite_interpolation := by
    intro x M hM hMx
    rcases B.interpolation x M hM hMx with ⟨z, hMz, hzx⟩
    exact ⟨z, hzx, hMz⟩
  upper_left := by
    intro x x' y hxx' hxy
    exact B.trans hxy hxx'
  rounded := by
    intro x y hxy
    rcases B.interpolation x {y} (Set.finite_singleton y) (by
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact hxy) with ⟨z, hyz, hzx⟩
    exact ⟨z, hzx, hyz y (by simp)⟩

/-- Relational composition of approximable relations. -/
noncomputable def approximableComp {B C D : AbstractBasis.{u}}
    (R : B.ApproximableRelation C) (S : C.ApproximableRelation D) :
    B.ApproximableRelation D where
  rel x z := ∃ y : C.carrier, R.rel x y ∧ S.rel y z
  lower_right := by
    rintro x z z' ⟨y, hR, hS⟩ hzz'
    exact ⟨y, hR, S.lower_right hS hzz'⟩
  finite_interpolation := by
    intro x M hM hXM
    classical
    let pick : {z : D.carrier // z ∈ M} → C.carrier := fun z =>
      Classical.choose (hXM z z.property)
    have hPick : ∀ z : {z : D.carrier // z ∈ M},
        R.rel x (pick z) ∧ S.rel (pick z) z := fun z =>
      Classical.choose_spec (hXM z z.property)
    letI : Fintype {z : D.carrier // z ∈ M} := hM.fintype
    let Y : Set C.carrier := Set.range pick
    have hYfinite : Y.Finite := Set.finite_range pick
    have hRY : ∀ y ∈ Y, R.rel x y := by
      intro y hy
      rcases hy with ⟨z, rfl⟩
      exact (hPick z).1
    rcases R.finite_interpolation x Y hYfinite hRY with ⟨y, hRxy, hYy⟩
    have hSyM : ∀ z ∈ M, S.rel y z := by
      intro z hz
      let z' : {z : D.carrier // z ∈ M} := ⟨z, hz⟩
      exact S.upper_left (hYy (pick z') ⟨z', rfl⟩) (hPick z').2
    rcases S.finite_interpolation y M hM hSyM with ⟨w, hSyw, hMw⟩
    exact ⟨w, ⟨y, hRxy, hSyw⟩, hMw⟩
  upper_left := by
    rintro x x' z hxx' ⟨y, hR, hS⟩
    exact ⟨y, R.upper_left hxx' hR, hS⟩
  rounded := by
    rintro x z ⟨y, hR, hS⟩
    rcases R.rounded hR with ⟨x', hx'x, hRx'⟩
    exact ⟨x', hx'x, y, hRx', hS⟩

@[ext]
theorem ApproximableRelation.ext {B C : AbstractBasis.{u}}
    {R S : B.ApproximableRelation C}
    (h : ∀ x y, R.rel x y ↔ S.rel x y) : R = S := by
  cases R with
  | mk r rlower rfinite rupper rrounded =>
      cases S with
      | mk s slower sfinite supper srounded =>
          have hrs : r = s := funext fun x => funext fun y => propext (h x y)
          subst s
          rfl

/-- The category of abstract bases and approximable relations. -/
noncomputable instance abstractBasisCategory : CategoryTheory.Category AbstractBasis.{u} where
  Hom B C := B.ApproximableRelation C
  id B := approximableId B
  comp R S := approximableComp R S
  id_comp := by
    intro B C R
    apply ApproximableRelation.ext
    intro x z
    constructor
    · rintro ⟨y, hyx, hRyz⟩
      exact R.upper_left hyx hRyz
    · intro hRxz
      rcases R.rounded hRxz with ⟨y, hyx, hRyz⟩
      exact ⟨y, hyx, hRyz⟩
  comp_id := by
    intro B C R
    apply ApproximableRelation.ext
    intro x z
    constructor
    · rintro ⟨y, hRxy, hzy⟩
      exact R.lower_right hRxy hzy
    · intro hRxz
      rcases R.finite_interpolation x {z} (Set.finite_singleton z) (by
        intro y hy
        rcases Set.mem_singleton_iff.mp hy with rfl
        exact hRxz) with ⟨y, hRxy, hzy⟩
      exact ⟨y, hRxy, hzy z (by simp)⟩
  assoc := by
    intro A B C D R S T
    apply ApproximableRelation.ext
    intro x w
    constructor
    · rintro ⟨z, ⟨y, hRxy, hSyz⟩, hTzw⟩
      exact ⟨y, hRxy, z, hSyz, hTzw⟩
    · rintro ⟨y, hRxy, z, hSyz, hTzw⟩
      exact ⟨z, ⟨y, hRxy, hSyz⟩, hTzw⟩

/-- Continuous maps between the local continuous-domain objects used in the
categorical statement of Theorem 2.2.28. -/
structure ContinuousDomainHom (D E : ContinuousDomainObject.{u}) where
  toFun : D.carrier → E.carrier
  continuous : @ScottContinuous D.carrier D.preorder E.carrier E.preorder toFun

/-- Continuous maps between the local algebraic-domain objects used in the
categorical statement of Theorem 2.2.29. -/
structure AlgebraicDomainHom (D E : AlgebraicDomainObject.{u}) where
  toFun : D.carrier → E.carrier
  continuous : @ScottContinuous D.carrier D.preorder E.carrier E.preorder toFun

namespace ContinuousDomainHom

def id (D : ContinuousDomainObject.{u}) : ContinuousDomainHom D D where
  toFun := fun x => x
  continuous := @scottContinuous_id D.carrier D.preorder

def comp {D E F : ContinuousDomainObject.{u}}
    (f : ContinuousDomainHom D E) (g : ContinuousDomainHom E F) :
    ContinuousDomainHom D F where
  toFun := fun x => g.toFun (f.toFun x)
  continuous := @ScottContinuous.comp D.carrier D.preorder E.carrier E.preorder
    F.carrier F.preorder g.toFun f.toFun g.continuous f.continuous

@[ext]
theorem ext {D E : ContinuousDomainObject.{u}} {f g : ContinuousDomainHom D E}
    (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  cases h
  rfl

end ContinuousDomainHom

/-- The category of bundled continuous dcpos and Scott-continuous maps. -/
instance continuousDomainCategory : CategoryTheory.Category ContinuousDomainObject.{u} where
  Hom := ContinuousDomainHom
  id := ContinuousDomainHom.id
  comp := ContinuousDomainHom.comp
  id_comp := by intros; apply ContinuousDomainHom.ext; rfl
  comp_id := by intros; apply ContinuousDomainHom.ext; rfl
  assoc := by intros; apply ContinuousDomainHom.ext; rfl

namespace AlgebraicDomainHom

def id (D : AlgebraicDomainObject.{u}) : AlgebraicDomainHom D D where
  toFun := fun x => x
  continuous := @scottContinuous_id D.carrier D.preorder

def comp {D E F : AlgebraicDomainObject.{u}}
    (f : AlgebraicDomainHom D E) (g : AlgebraicDomainHom E F) :
    AlgebraicDomainHom D F where
  toFun := fun x => g.toFun (f.toFun x)
  continuous := @ScottContinuous.comp D.carrier D.preorder E.carrier E.preorder
    F.carrier F.preorder g.toFun f.toFun g.continuous f.continuous

@[ext]
theorem ext {D E : AlgebraicDomainObject.{u}} {f g : AlgebraicDomainHom D E}
    (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  cases h
  rfl

end AlgebraicDomainHom

/-- The category of bundled algebraic dcpos and Scott-continuous maps. -/
instance algebraicDomainCategory : CategoryTheory.Category AlgebraicDomainObject.{u} where
  Hom := AlgebraicDomainHom
  id := AlgebraicDomainHom.id
  comp := AlgebraicDomainHom.comp
  id_comp := by intros; apply AlgebraicDomainHom.ext; rfl
  comp_id := by intros; apply AlgebraicDomainHom.ext; rfl
  assoc := by intros; apply AlgebraicDomainHom.ext; rfl

/-- Reflexive abstract bases, i.e. the preorders in Theorem 2.2.29. -/
abbrev ReflexiveAbstractBasis : Type (u + 1) :=
  {B : AbstractBasis.{u} // ∀ x : B.carrier, B.rel x x}

/-- The full category of reflexive abstract bases, with approximable relations
as morphisms. -/
noncomputable instance reflexiveAbstractBasisCategory :
    CategoryTheory.Category ReflexiveAbstractBasis.{u} where
  Hom B C := B.1.ApproximableRelation C.1
  id B := approximableId B.1
  comp R S := approximableComp R S
  id_comp := by
    intro B C R
    apply ApproximableRelation.ext
    intro x z
    constructor
    · rintro ⟨y, hyx, hRyz⟩
      exact R.upper_left hyx hRyz
    · intro hRxz
      rcases R.rounded hRxz with ⟨y, hyx, hRyz⟩
      exact ⟨y, hyx, hRyz⟩
  comp_id := by
    intro B C R
    apply ApproximableRelation.ext
    intro x z
    constructor
    · rintro ⟨y, hRxy, hzy⟩
      exact R.lower_right hRxy hzy
    · intro hRxz
      rcases R.finite_interpolation x {z} (Set.finite_singleton z) (by
        intro y hy
        rcases Set.mem_singleton_iff.mp hy with rfl
        exact hRxz) with ⟨y, hRxy, hzy⟩
      exact ⟨y, hRxy, hzy z (by simp)⟩
  assoc := by
    intro A B C D R S T
    apply ApproximableRelation.ext
    intro x w
    constructor
    · rintro ⟨z, ⟨y, hRxy, hSyz⟩, hTzw⟩
      exact ⟨y, hRxy, z, hSyz, hTzw⟩
    · rintro ⟨y, hRxy, z, hSyz, hTzw⟩
      exact ⟨z, ⟨y, hRxy, hSyz⟩, hTzw⟩

/-- The PDF-level categorical equivalence statement of Theorem 2.2.28, using
mathlib's bundled equivalence of categories. -/
def Theorem228CategoricalEquivalence : Prop :=
  Nonempty (CategoryTheory.Equivalence AbstractBasis.{u} ContinuousDomainObject.{u})

/-- The PDF-level categorical equivalence statement of Theorem 2.2.29, using
mathlib's bundled equivalence of categories. -/
def Theorem229CategoricalEquivalence : Prop :=
  Nonempty (CategoryTheory.Equivalence ReflexiveAbstractBasis.{u} AlgebraicDomainObject.{u})

/-- Auxiliary presentation-object equivalence retained for the explicit local
presentation used around Theorem 2.2.28.  This is not the PDF-facing categorical
equivalence theorem. -/
theorem theorem_2_2_28_presentation_object_equiv :
    Nonempty (AbstractBasis.{u} ≃ ContinuousDomainPresentationObject.{u}) := by
  refine ⟨{
    toFun := fun B => { basisObject := B }
    invFun := fun X => X.basisObject
    left_inv := ?_
    right_inv := ?_
  }⟩
  · intro B
    rfl
  · intro X
    cases X
    rfl

/-- Theorem 2.2.28 (PDF): "The category of abstract bases and approximable
relations is equivalent to CONT, the category of continuous dcpo's and
continuous maps."  The book says this is proved without difficulties but gives
no proof and no external source here, so this remains explicit book-omitted
proof debt rather than an external axiom. -/
theorem theorem_2_2_28_abstract_bases_equiv_CONT : Theorem228CategoricalEquivalence.{u} := by
  admit

/-- Auxiliary presentation-object equivalence retained for the explicit local
presentation used around Theorem 2.2.29.  This is not the PDF-facing categorical
equivalence theorem. -/
theorem theorem_2_2_29_presentation_object_equiv :
    Nonempty (ReflexiveAbstractBasis.{u} ≃ AlgebraicDomainPresentationObject.{u}) := by
  refine ⟨{
    toFun := fun B => { basisObject := B.1, reflexive := B.2 }
    invFun := fun X => ⟨X.basisObject, X.reflexive⟩
    left_inv := ?_
    right_inv := ?_
  }⟩
  · intro B
    cases B
    rfl
  · intro X
    cases X
    rfl

/-- Theorem 2.2.29 (PDF): "The category of preorders and approximable relations
is equivalent to ALG, the category of algebraic dcpo's and continuous maps."
The book says this follows immediately from the preceding formulation but gives
no proof and no external source here, so this remains explicit book-omitted
proof debt rather than an external axiom. -/
theorem theorem_2_2_29_preorders_equiv_ALG : Theorem229CategoricalEquivalence.{u} := by
  admit

end AbstractBasis

end AbstractBases

section NumberedCoverageTopology

variable {α : Type u} [Preorder α]

/-- Definition 2.3.1: membership in the Scott interior of a set. -/
def ScottInteriorMem (A : Set α) (x : α) : Prop :=
  ∃ O : Set α, ScottOpen O ∧ O ⊆ A ∧ x ∈ O

/-- Definition 2.3.1: Scott neighborhoods. -/
def ScottNeighborhood (x : α) (O : Set α) : Prop :=
  ScottOpen O ∧ x ∈ O

/-- Proposition 2.3.2(2), local preorder form: the Scott topology is T0 under
the explicit antisymmetry hypothesis used by this file's preorder encoding. -/
theorem prop_2_3_2_2_scott_T0 {x y : α}
    (hanti : ∀ ⦃a b : α⦄, a ≤ b → b ≤ a → a = b)
    (hxy : x ≠ y) :
    (∃ O : Set α, ScottOpen O ∧ ((x ∈ O ∧ y ∉ O) ∨ (y ∈ O ∧ x ∉ O))) := by
  classical
  by_cases hle : x ≤ y
  · have hnot : ¬ y ≤ x := by
      intro hyx
      exact hxy (hanti hle hyx)
    let O : Set α := (lowerClosure ({x} : Set α))ᶜ
    have hO : ScottOpen O := by
      simpa [O, ScottOpen] using scottClosed_principal_ideal x
    have hyO : y ∈ O := by
      intro hy
      rcases hy with ⟨z, hz, hyz⟩
      have hzx : z = x := by simpa using hz
      exact hnot (by simpa [hzx] using hyz)
    have hxO : x ∉ O := by
      intro hx
      exact hx ⟨x, by simp, le_rfl⟩
    exact ⟨O, hO, Or.inr ⟨hyO, hxO⟩⟩
  · let O : Set α := (lowerClosure ({y} : Set α))ᶜ
    have hO : ScottOpen O := by
      simpa [O, ScottOpen] using scottClosed_principal_ideal y
    have hxO : x ∈ O := by
      intro hx
      rcases hx with ⟨z, hz, hxz⟩
      have hzy : z = y := by simpa using hz
      exact hle (by simpa [hzy] using hxz)
    have hyO : y ∉ O := by
      intro hy
      exact hy ⟨y, by simp, le_rfl⟩
    exact ⟨O, hO, Or.inl ⟨hxO, hyO⟩⟩

/-- Proposition 2.3.2(3): Scott topology is Hausdorff exactly for the trivial
order. -/
theorem prop_2_3_2_3_scott_hausdorff_trivial_order :
    (∀ x y : α, x ≠ y →
      ∃ U V : Set α, ScottOpen U ∧ ScottOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V) ↔
    (∀ x y : α, x ≤ y → x = y) := by
  constructor
  · intro hHaus x y hxy
    by_contra hne
    rcases hHaus x y hne with ⟨U, V, hU, hV, hxU, hyV, hdis⟩
    have hyU : y ∈ U := scottOpen_upper hU hxU hxy
    exact Set.disjoint_left.mp hdis hyU hyV
  · intro htriv x y hxy
    have hsingleton : ∀ z : α, ScottOpen ({z} : Set α) := by
      intro z
      constructor
      · intro a b hb hab haz
        exact hb ((htriv a b hab).symm.trans haz)
      · intro A s hA hAs hs hsz
        rcases hA.1 with ⟨a, ha⟩
        have has : a ≤ s := hs.1 ha
        exact hAs ha ((htriv a s has).trans hsz)
    exact ⟨{x}, {y}, hsingleton x, hsingleton y, by simp, by simp,
      Set.disjoint_singleton.mpr hxy⟩

/-- Proposition 2.3.3: directed suprema are characterized by Scott neighborhoods. -/
theorem prop_2_3_3_sup_iff_neighborhoods
    {A : Set α} {x : α} (hA : DirectedSet A) :
    IsSup A x ↔
      IsUpperBound A x ∧
        ∀ O : Set α, ScottNeighborhood x O → ∃ a ∈ A, a ∈ O := by
  constructor
  · intro hx
    constructor
    · exact hx.1
    · intro O hO
      by_contra hnone
      have hAcompl : A ⊆ Oᶜ := by
        intro a ha haO
        exact hnone ⟨a, ha, haO⟩
      have hxcompl : x ∈ Oᶜ := hO.1.2 hA hAcompl hx
      exact hxcompl hO.2
  · intro h
    constructor
    · exact h.1
    · intro y hy
      apply prop_2_3_2_open_to_order
      intro O hO hxO
      rcases h.2 O ⟨hO, hxO⟩ with ⟨a, ha, haO⟩
      exact scottOpen_upper hO haO (hy ha)

/-- Proposition 2.3.4, preorder/existing-suprema form: order-theoretic and
topological Scott-continuity coincide for the unbundled Scott topologies. -/
theorem prop_2_3_4_scottContinuous_iff_topological
    {β : Type v} [Preorder β] {f : α → β} :
    ScottContinuous f ↔ TopologicallyScottContinuous f := by
  constructor
  · exact prop_2_3_4_forward
  · intro hf
    have hmono : Monotone f := by
      intro x y hxy
      apply prop_2_3_2_open_to_order
      intro O hO hfxO
      exact prop_2_3_2_order_to_open hxy (f ⁻¹' O) (hf O hO) hfxO
    constructor
    · exact hmono
    · intro A x hA hx
      constructor
      · intro y hy
        rcases hy with ⟨a, ha, rfl⟩
        exact hmono (hx.1 ha)
      · intro y hy
        apply prop_2_3_2_open_to_order
        intro O hO hfxO
        rcases (prop_2_3_3_sup_iff_neighborhoods hA).1 hx |>.2
            (f ⁻¹' O) ⟨hf O hO, hfxO⟩ with
          ⟨a, ha, hfaO⟩
        exact scottOpen_upper hO hfaO (hy ⟨a, ha, rfl⟩)

/-- In a continuous domain, `↑↑x` is Scott-open. -/
theorem scottOpen_wayBelowUpper
    (hcont : IsContinuousDomain α) (x : α) :
    ScottOpen (wayBelowUpper x) := by
  constructor
  · intro a b hb hab hxa
    exact hb (prop_2_2_2_2 le_rfl hxa hab)
  · intro A s hA hAs hs hxs
    rcases cor_2_2_16_wayBelow_directed_sup hcont hA hs hxs with
      ⟨a, ha, hxa⟩
    exact hAs ha hxa

/-- Proposition 2.3.5: approximation equals membership in the Scott interior of a
principal upper set in continuous domains. -/
theorem prop_2_3_5_wayBelow_iff_scottInterior
    (hcont : IsContinuousDomain α) {x y : α} :
    x ≪ y ↔ ScottInteriorMem (upperClosure ({x} : Set α)) y := by
  have hWayBelowOpen : ScottOpen (wayBelowUpper x) :=
    scottOpen_wayBelowUpper hcont x
  constructor
  · intro hxy
    exact ⟨wayBelowUpper x, hWayBelowOpen, (by
      intro z hz
      exact ⟨x, by simp, prop_2_2_2_1 hz⟩), hxy⟩
  · intro hy
    rcases hy with ⟨O, hO, hOsub, hyO⟩
    intro A s hA hs hys
    have hsO : s ∈ O := scottOpen_upper hO hyO hys
    rcases (prop_2_3_3_sup_iff_neighborhoods hA).1 hs |>.2 O ⟨hO, hsO⟩ with
      ⟨a, ha, haO⟩
    rcases hOsub haO with ⟨z, hz, hza⟩
    have hzx : z = x := by simpa using hz
    exact ⟨a, ha, by simpa [hzx] using hza⟩

/-- Proposition 2.3.5: approximation equals membership in `↑↑x`. -/
theorem prop_2_3_5_wayBelow_iff_wayBelowUpper
    {x y : α} :
    x ≪ y ↔ y ∈ wayBelowUpper x := by
  rfl

/-- Proposition 2.3.6(2): every Scott-open set is supported by basis elements. -/
theorem prop_2_3_6_open_supported_by_basis
    {B O : Set α} (hB : IsBasis B) (hO : ScottOpen O) :
    O = ⋃ x ∈ O ∩ B, wayBelowUpper x := by
  ext y
  constructor
  · intro hy
    have hdir : DirectedSet (Approximants B y) := (hB y).1
    have hsup : IsSup (Approximants B y) y := (hB y).2
    by_contra hnot
    have hcomp : Approximants B y ⊆ Oᶜ := by
      intro b hb hbO
      have hyInUnion : y ∈ ⋃ x ∈ O ∩ B, wayBelowUpper x := by
        rw [Set.mem_iUnion]
        refine ⟨b, ?_⟩
        rw [Set.mem_iUnion]
        exact ⟨⟨hbO, hb.1⟩, hb.2⟩
      exact hnot hyInUnion
    have hyComp : y ∈ Oᶜ := hO.2 hdir hcomp hsup
    exact hyComp hy
  · intro hy
    rw [Set.mem_iUnion] at hy
    rcases hy with ⟨x, hxrest⟩
    rw [Set.mem_iUnion] at hxrest
    rcases hxrest with ⟨hxOB, hxy⟩
    exact scottOpen_upper hO hxOB.1 (prop_2_2_2_1 hxy)

namespace AbstractBasis

variable (B : AbstractBasis.{u})

/-- Proposition 2.3.7: the observable open
`{A : Idl(B) | ∃ x ∈ M, x ∈ A}` generated by a set of abstract-basis elements. -/
def observableOpen (M : Set B.carrier) : Set B.Ideal :=
  {A : B.Ideal | ∃ x ∈ M, x ∈ A.1}

/-- Proposition 2.3.7: all Scott-opens of an ideal completion arise from subsets
of the basis. -/
theorem prop_2_3_7_ideal_completion_opens (M : Set B.carrier) :
    ScottOpen (B.observableOpen M) ∧
      ∀ O : Set B.Ideal, ScottOpen O → ∃ M : Set B.carrier, O = B.observableOpen M := by
  constructor
  · constructor
    · intro A C hC hAC hA
      rcases hA with ⟨x, hxM, hxA⟩
      exact hC ⟨x, hxM, hAC hxA⟩
    · intro A s hA hAcompl hs hsobs
      rcases hsobs with ⟨x, hxM, hxs⟩
      let U : B.Ideal := ⟨{y : B.carrier | ∃ I ∈ A, y ∈ I.1}, B.directedUnionIdeal hA⟩
      have hUupper : IsUpperBound A U := by
        intro I hI y hyI
        exact ⟨I, hI, hyI⟩
      have hsU : s ≤ U := hs.2 U hUupper
      rcases hsU hxs with ⟨I, hI, hxI⟩
      exact hAcompl hI ⟨x, hxM, hxI⟩
  · intro O hO
    let M : Set B.carrier := {x | B.principalIdeal x ∈ O}
    refine ⟨M, ?_⟩
    ext A
    constructor
    · intro hAO
      have hBasis : IsBasis (Set.range B.principalIdeal) :=
        prop_2_2_4_1 B.principalIdealBasisRaw
      have hcover := prop_2_3_6_open_supported_by_basis
        (α := B.Ideal) hBasis hO
      rw [hcover] at hAO
      rw [Set.mem_iUnion] at hAO
      rcases hAO with ⟨I, hrest⟩
      rw [Set.mem_iUnion] at hrest
      rcases hrest with ⟨hIOBasis, hIA⟩
      rcases hIOBasis.2 with ⟨x, rfl⟩
      rcases (B.prop_2_2_22_2_ideal_wayBelow
          (A := B.principalIdeal x) (A' := A)).1 hIA with
        ⟨y, hyA, hx_y⟩
      have hyO : B.principalIdeal y ∈ O :=
        scottOpen_upper hO hIOBasis.1 hx_y
      exact ⟨y, hyO, hyA⟩
    · intro hAobs
      rcases hAobs with ⟨x, hxM, hxA⟩
      have hxA_le : B.principalIdeal x ≤ A := by
        intro y hy
        exact A.property.1 hxA hy
      exact scottOpen_upper hO hxM hxA_le

end AbstractBasis

/-- Definition 2.3.1 topology law: arbitrary unions of Scott-open sets are
Scott-open. -/
theorem scottOpen_iUnion
    {ι : Type v} {U : ι → Set α} (hU : ∀ i : ι, ScottOpen (U i)) :
    ScottOpen (Set.iUnion U) := by
  constructor
  · intro x y hy hxy hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨i, hxi⟩
    exact hy (by
      rw [Set.mem_iUnion]
      exact ⟨i, scottOpen_upper (hU i) hxi hxy⟩)
  · intro A s hA hAs hs hsU
    rw [Set.mem_iUnion] at hsU
    rcases hsU with ⟨i, hsi⟩
    have hsComp : s ∈ (U i)ᶜ := (hU i).2 hA (by
      intro a ha hai
      exact hAs ha (by
        rw [Set.mem_iUnion]
        exact ⟨i, hai⟩)) hs
    exact hsComp hsi

/-- The Scott topology packaged as mathlib's `TopologicalSpace`.  The unbundled
`ScottOpen` predicate remains the source-facing definition, while this bridge
allows later library code to use the standard topology API. -/
@[reducible]
def scottTopologicalSpace : TopologicalSpace α where
  IsOpen := ScottOpen
  isOpen_univ := scottOpen_univ
  isOpen_inter := fun _ _ => scottOpen_inter
  isOpen_sUnion := by
    intro S hS
    have hOpen : ScottOpen (⋃ U : S, (U.1 : Set α)) :=
      scottOpen_iUnion (fun U : S => hS U.1 U.2)
    have hEq : (⋃ U : S, (U.1 : Set α)) = ⋃₀ S := by
      ext x
      constructor
      · intro hx
        rw [Set.mem_iUnion] at hx
        rcases hx with ⟨U, hxU⟩
        exact Set.mem_sUnion_of_mem hxU U.2
      · intro hx
        rcases Set.mem_sUnion.mp hx with ⟨U, hUS, hxU⟩
        rw [Set.mem_iUnion]
        exact ⟨⟨U, hUS⟩, hxU⟩
    simpa [hEq] using hOpen

theorem isOpen_scottTopologicalSpace_iff {O : Set α} :
    @IsOpen α scottTopologicalSpace O ↔ ScottOpen O :=
  Iff.rfl

/-- Proposition 2.3.6, full iff form: in a continuous domain with basis `B`,
Scott openness is equivalent to each of the two way-below union descriptions
given in the book. -/
theorem prop_2_3_6_scottOpen_iff_supported
    (hcont : IsContinuousDomain α) {B O : Set α} (hB : IsBasis B) :
    ScottOpen O ↔
      O = ⋃ x ∈ O, wayBelowUpper x ∧
        O = ⋃ x ∈ O ∩ B, wayBelowUpper x := by
  constructor
  · intro hO
    exact ⟨prop_2_3_6_open_supported_by_wayBelow hcont hO,
      prop_2_3_6_open_supported_by_basis hB hO⟩
  · rintro ⟨hO, _⟩
    rw [hO]
    constructor
    · intro a b hb hab ha
      rw [Set.mem_iUnion] at ha
      rcases ha with ⟨x, ha⟩
      rw [Set.mem_iUnion] at ha
      rcases ha with ⟨hxO, hxa⟩
      exact hb (by
        rw [Set.mem_iUnion]
        refine ⟨x, ?_⟩
        rw [Set.mem_iUnion]
        exact ⟨hxO, scottOpen_upper (scottOpen_wayBelowUpper hcont x) hxa hab⟩)
    · intro A s hA hAs hs hsUnion
      rw [Set.mem_iUnion] at hsUnion
      rcases hsUnion with ⟨x, hsUnion⟩
      rw [Set.mem_iUnion] at hsUnion
      rcases hsUnion with ⟨hxO, hxs⟩
      have hsComp : s ∈ (wayBelowUpper x)ᶜ :=
        (scottOpen_wayBelowUpper hcont x).2 hA (by
          intro a ha hax
          exact hAs ha (by
            rw [Set.mem_iUnion]
            refine ⟨x, ?_⟩
            rw [Set.mem_iUnion]
            exact ⟨hxO, hax⟩)) hs
      exact hsComp hxs

/-- The first point in an interpolating sequence between `y` and `x`. -/
noncomputable def wayBelowInterpSeed
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) :
    {z : α // y ≪ z} :=
  ⟨Classical.choose (wayBelow_interpolation hcont hyx),
    (Classical.choose_spec (wayBelow_interpolation hcont hyx)).1⟩

theorem wayBelowInterpSeed_wayBelow_target
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) :
    (wayBelowInterpSeed hcont hyx).1 ≪ x :=
  (Classical.choose_spec (wayBelow_interpolation hcont hyx)).2

/-- One interpolation step, keeping the lower endpoint `y` fixed. -/
noncomputable def wayBelowInterpStep
    (hcont : IsContinuousDomain α) {y : α} (p : {z : α // y ≪ z}) :
    {z : α // y ≪ z} :=
  ⟨Classical.choose (wayBelow_interpolation hcont p.2),
    (Classical.choose_spec (wayBelow_interpolation hcont p.2)).1⟩

theorem wayBelowInterpStep_wayBelow_prev
    (hcont : IsContinuousDomain α) {y : α} (p : {z : α // y ≪ z}) :
    (wayBelowInterpStep hcont p).1 ≪ p.1 :=
  (Classical.choose_spec (wayBelow_interpolation hcont p.2)).2

/-- The interpolating sequence used in Lemma 2.3.8. -/
noncomputable def wayBelowInterpPoint
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) :
    Nat → {z : α // y ≪ z}
  | 0 => wayBelowInterpSeed hcont hyx
  | n + 1 => wayBelowInterpStep hcont (wayBelowInterpPoint hcont hyx n)

/-- Values of the interpolating sequence. -/
noncomputable def wayBelowInterpSeq
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) :
    Nat → α :=
  fun n => (wayBelowInterpPoint hcont hyx n).1

theorem wayBelowInterpSeq_source_wayBelow
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) (n : Nat) :
    y ≪ wayBelowInterpSeq hcont hyx n := by
  exact (wayBelowInterpPoint hcont hyx n).2

theorem wayBelowInterpSeq_zero_wayBelow_target
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) :
    wayBelowInterpSeq hcont hyx 0 ≪ x := by
  exact wayBelowInterpSeed_wayBelow_target hcont hyx

theorem wayBelowInterpSeq_succ_wayBelow
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) (n : Nat) :
    wayBelowInterpSeq hcont hyx (n + 1) ≪ wayBelowInterpSeq hcont hyx n := by
  exact wayBelowInterpStep_wayBelow_prev hcont (wayBelowInterpPoint hcont hyx n)

theorem wayBelowInterpSeq_succ_le
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) (n : Nat) :
    wayBelowInterpSeq hcont hyx (n + 1) ≤ wayBelowInterpSeq hcont hyx n :=
  prop_2_2_2_1 (wayBelowInterpSeq_succ_wayBelow hcont hyx n)

theorem wayBelowInterpSeq_le_of_le
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x)
    {m n : Nat} (hmn : m ≤ n) :
    wayBelowInterpSeq hcont hyx n ≤ wayBelowInterpSeq hcont hyx m := by
  induction hmn with
  | refl => exact le_rfl
  | step hmn ih =>
      exact le_trans (wayBelowInterpSeq_succ_le hcont hyx _) ih

/-- The filter generated by the interpolating sequence. -/
noncomputable def interpolatingFilter
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) : Set α :=
  Set.iUnion fun n : Nat => wayBelowUpper (wayBelowInterpSeq hcont hyx n)

theorem interpolatingFilter_scottOpen
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) :
    ScottOpen (interpolatingFilter hcont hyx) := by
  exact scottOpen_iUnion (fun n =>
    scottOpen_wayBelowUpper hcont (wayBelowInterpSeq hcont hyx n))

theorem interpolatingFilter_isFilter
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) :
    IsFilter (interpolatingFilter hcont hyx) := by
  constructor
  · intro a b ha hab
    rw [interpolatingFilter, Set.mem_iUnion] at ha ⊢
    rcases ha with ⟨n, hna⟩
    exact ⟨n, prop_2_2_2_2 le_rfl hna hab⟩
  · constructor
    · refine ⟨x, ?_⟩
      rw [interpolatingFilter, Set.mem_iUnion]
      exact ⟨0, wayBelowInterpSeq_zero_wayBelow_target hcont hyx⟩
    · intro a ha b hb
      rw [interpolatingFilter, Set.mem_iUnion] at ha hb
      rcases ha with ⟨m, hma⟩
      rcases hb with ⟨n, hnb⟩
      let k : Nat := Nat.max m n + 1
      have hmk : m ≤ k := Nat.le_trans (Nat.le_max_left m n) (Nat.le_succ _)
      have hnk : n ≤ k := Nat.le_trans (Nat.le_max_right m n) (Nat.le_succ _)
      refine ⟨wayBelowInterpSeq hcont hyx k, ?_, ?_, ?_⟩
      · rw [interpolatingFilter, Set.mem_iUnion]
        exact ⟨k + 1, wayBelowInterpSeq_succ_wayBelow hcont hyx k⟩
      · exact le_trans (wayBelowInterpSeq_le_of_le hcont hyx hmk)
          (prop_2_2_2_1 hma)
      · exact le_trans (wayBelowInterpSeq_le_of_le hcont hyx hnk)
          (prop_2_2_2_1 hnb)

theorem interpolatingFilter_mem_target
    (hcont : IsContinuousDomain α) {y x : α} (hyx : y ≪ x) :
    x ∈ interpolatingFilter hcont hyx := by
  rw [interpolatingFilter, Set.mem_iUnion]
  exact ⟨0, wayBelowInterpSeq_zero_wayBelow_target hcont hyx⟩

theorem interpolatingFilter_subset_open
    (hcont : IsContinuousDomain α) {O : Set α} (hO : ScottOpen O)
    {y x : α} (hyO : y ∈ O) (hyx : y ≪ x) :
    interpolatingFilter hcont hyx ⊆ O := by
  intro z hz
  rw [interpolatingFilter, Set.mem_iUnion] at hz
  rcases hz with ⟨n, hnz⟩
  have hy_seq : y ≤ wayBelowInterpSeq hcont hyx n :=
    prop_2_2_2_1 (wayBelowInterpSeq_source_wayBelow hcont hyx n)
  have hseq_z : wayBelowInterpSeq hcont hyx n ≤ z := prop_2_2_2_1 hnz
  exact scottOpen_upper hO (scottOpen_upper hO hyO hy_seq) hseq_z

/-- Lemma 2.3.8: Scott-open sets in continuous domains are unions of Scott-open
filters. -/
theorem lemma_2_3_8_scott_open_union_filters
    (hcont : IsContinuousDomain α) {O : Set α} (hO : ScottOpen O) :
    ∃ F : Set (Set α),
      (∀ V ∈ F, ScottOpen V ∧ IsFilter V) ∧ O = ⋃₀ F := by
  let F : Set (Set α) :=
    {V | ∃ x ∈ O, ∃ y ∈ O, ∃ hyx : y ≪ x, V = interpolatingFilter hcont hyx}
  refine ⟨F, ?_, ?_⟩
  · intro V hV
    rcases hV with ⟨x, hxO, y, hyO, hyx, rfl⟩
    exact ⟨interpolatingFilter_scottOpen hcont hyx,
      interpolatingFilter_isFilter hcont hyx⟩
  · ext x
    constructor
    · intro hxO
      have hcover := congrArg (fun S : Set α => x ∈ S)
        (prop_2_3_6_open_supported_by_wayBelow hcont hO)
      have hxUnion : x ∈ ⋃ y ∈ O, wayBelowUpper y := by
        simpa using hcover.mp hxO
      rw [Set.mem_iUnion] at hxUnion
      rcases hxUnion with ⟨y, hyrest⟩
      rw [Set.mem_iUnion] at hyrest
      rcases hyrest with ⟨hyO, hyx⟩
      exact ⟨interpolatingFilter hcont hyx,
        ⟨x, hxO, y, hyO, hyx, rfl⟩,
        interpolatingFilter_mem_target hcont hyx⟩
    · intro hxF
      rcases hxF with ⟨V, hVF, hxV⟩
      rcases hVF with ⟨x₀, _hx₀O, y, hyO, hyx₀, rfl⟩
      exact interpolatingFilter_subset_open hcont hO hyO hyx₀ hxV

end NumberedCoverageTopology
end Chapter2
end AbramskyJung

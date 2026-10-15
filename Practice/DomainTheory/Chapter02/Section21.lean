import Practice.DomainTheory.Topology.ScottTopology
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Topology.Defs.Basic

set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-!
# Abramsky--Jung, Domain Theory, Chapter 2: Section 2.1

Book-facing declarations are kept in source order. Reusable order-theoretic
interfaces remain in `Practice.DomainTheory.Order` and
`Practice.DomainTheory.Topology`.
-/

universe u v w

namespace AbramskyJung
namespace Chapter2

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

end Chapter2
end AbramskyJung

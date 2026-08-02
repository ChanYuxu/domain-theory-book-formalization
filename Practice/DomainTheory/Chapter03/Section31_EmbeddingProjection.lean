import Practice.DomainTheory.Chapter03.Section31_Adjunctions

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 3.1: embedding-projection pairs

This file contains the embedding-projection, kernel operator, and closure
operator material from Section 3.1.
-/

universe u v

namespace AbramskyJung
namespace Chapter3

section EmbeddingProjection

variable {D : Type u} [Preorder D]
variable {E : Type v} [Preorder E]

/-- Definition 3.1.15: continuous embedding-projection pairs. -/
structure EPPair (D : Type u) (E : Type v) [Preorder D] [Preorder E] where
  e : D → E
  p : E → D
  continuous_e : ScottContinuous e
  continuous_p : ScottContinuous p
  retract : ∀ x : D, p (e x) = x
  below : ∀ y : E, e (p y) ≤ y

namespace EPPair

variable (ep : EPPair D E)

/-- Every e-p-pair is an adjunction `e ⊣ p`. -/
theorem toAdjunction : Adjunction ep.e ep.p := by
  refine adjunction_of_unit_counit ep.continuous_e.1 ep.continuous_p.1 ?_ ?_
  · intro x
    simp [ep.retract x]
  · intro y
    exact ep.below y

/-- Embeddings are injective. -/
theorem embedding_injective : Function.Injective ep.e := by
  intro x y hxy
  have h := congrArg ep.p hxy
  simpa [ep.retract x, ep.retract y] using h

/-- Projections are surjective. -/
theorem projection_surjective : Function.Surjective ep.p := by
  intro x
  exact ⟨ep.e x, ep.retract x⟩

/-- Proposition 3.1.16: embeddings reflect and preserve way-below. -/
theorem wayBelow_iff {x y : D} : WayBelow (ep.e x) (ep.e y) ↔ WayBelow x y := by
  constructor
  · intro hxy A s hA hs hys
    have hesup : IsSup (ep.e '' A) (ep.e s) := ep.continuous_e.2 hA hs
    have heys : ep.e y ≤ ep.e s := ep.continuous_e.1 hys
    rcases hxy (DirectedSet.image ep.continuous_e.1 hA) hesup heys with ⟨ea, hea, hxea⟩
    rcases hea with ⟨a, ha, rfl⟩
    refine ⟨a, ha, ?_⟩
    calc
      x = ep.p (ep.e x) := (ep.retract x).symm
      _ ≤ ep.p (ep.e a) := ep.continuous_p.1 hxea
      _ = a := ep.retract a
  · intro hxy
    exact lower_adjoint_preserves_wayBelow ep.toAdjunction ep.continuous_p hxy

end EPPair

/-- Kernel operators/projections: continuous idempotents below the identity. -/
structure KernelOperator (D : Type u) [Preorder D] where
  k : D → D
  continuous : ScottContinuous k
  idem : ∀ x : D, k (k x) = k x
  below : ∀ x : D, k x ≤ x

namespace KernelOperator

variable (K : KernelOperator D)

/-- The image carrier of a kernel operator. -/
def ImageCarrier : Type u :=
  {x : D // x ∈ Set.range K.k}

instance imageCarrierPreorder : Preorder K.ImageCarrier where
  le x y := x.1 ≤ y.1
  le_refl x := le_rfl
  le_trans x y z hxy hyz := le_trans hxy hyz

/-- A kernel operator as a bundled Scott-continuous self-map. -/
def toScottContFun : Chapter2.ScottContFun D D :=
  { toFun := K.k, continuous := K.continuous }

/-- Inclusion of the kernel image into the ambient dcpo. -/
def inclusion : K.ImageCarrier → D :=
  fun x => x.1

/-- Projection from the ambient dcpo onto the kernel image. -/
def projection (x : D) : K.ImageCarrier :=
  ⟨K.k x, ⟨x, rfl⟩⟩

/-- Every `k x` lies in the image. -/
theorem apply_mem_range (x : D) : K.k x ∈ Set.range K.k :=
  ⟨x, rfl⟩

/-- Fixed-point characterization of the image. -/
theorem mem_range_iff_fixed {y : D} : y ∈ Set.range K.k ↔ K.k y = y := by
  constructor
  · intro hy
    rcases hy with ⟨x, rfl⟩
    exact K.idem x
  · intro hy
    exact ⟨y, hy⟩

/-- Proposition 3.1.17(2): `k x` is the greatest image element below `x`. -/
theorem le_kernel_of_mem_range_le {x y : D}
    (hy : y ∈ Set.range K.k) (hyx : y ≤ x) : y ≤ K.k x := by
  have hfix : K.k y = y := (K.mem_range_iff_fixed).1 hy
  calc
    y = K.k y := hfix.symm
    _ ≤ K.k x := K.continuous.1 hyx

/-- The projection is monotone. -/
theorem projection_monotone : Monotone K.projection := by
  intro x y hxy
  exact K.continuous.1 hxy

/-- The inclusion is monotone. -/
theorem inclusion_monotone : Monotone K.inclusion := by
  intro x y hxy
  exact hxy

/-- Projecting a point already in the image returns it. -/
theorem projection_inclusion_eq (x : K.ImageCarrier) :
    K.projection x.1 = x := by
  apply Subtype.ext
  exact (K.mem_range_iff_fixed).1 x.2

/-- The inclusion after projection is the kernel map. -/
theorem inclusion_projection_eq (x : D) :
    K.inclusion (K.projection x) = K.k x := rfl

/-- The projection onto a kernel image is Scott-continuous. -/
theorem projection_scottContinuous : ScottContinuous K.projection := by
  constructor
  · exact K.projection_monotone
  · intro A x hA hx
    have hksup : IsSup (K.k '' A) (K.k x) := K.continuous.2 hA hx
    constructor
    · intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      exact hksup.1 ⟨a, ha, rfl⟩
    · intro y hy
      exact hksup.2 y.1 (by
        intro z hz
        rcases hz with ⟨a, ha, rfl⟩
        exact hy ⟨a, ha, rfl⟩)

/-- The inclusion of a kernel image is Scott-continuous. -/
theorem inclusion_scottContinuous : ScottContinuous K.inclusion := by
  constructor
  · exact K.inclusion_monotone
  · intro A s hA hs
    constructor
    · intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      exact hs.1 ha
    · intro y hy
      have hprojUpper : IsUpperBound A (K.projection y) := by
        intro a ha
        exact K.le_kernel_of_mem_range_le a.2 (hy ⟨a, ha, rfl⟩)
      exact le_trans (hs.2 (K.projection y) hprojUpper) (K.below y)

/-- The kernel-image inclusion is left adjoint to the projection. -/
theorem inclusion_projection_adjunction :
    Adjunction K.inclusion K.projection := by
  refine ⟨?_⟩
  intro x y
  constructor
  · intro hxy
    exact le_trans hxy (K.below y)
  · intro hxy
    exact K.le_kernel_of_mem_range_le x.2 hxy

/-- Proposition 3.1.17(4): the way-below relation on the image is the
restriction of the ambient way-below relation. -/
theorem image_wayBelow_iff {x y : K.ImageCarrier} :
    WayBelow x y ↔ WayBelow x.1 y.1 := by
  constructor
  · intro hxy
    exact lower_adjoint_preserves_wayBelow
      K.inclusion_projection_adjunction K.projection_scottContinuous hxy
  · intro hxy A s hA hs hys
    have hvalSup : IsSup (K.inclusion '' A) (K.inclusion s) :=
      K.inclusion_scottContinuous.2 hA hs
    have hvalDir : DirectedSet (K.inclusion '' A) :=
      DirectedSet.image K.inclusion_scottContinuous.1 hA
    rcases hxy hvalDir hvalSup hys with ⟨a, ha, hxa⟩
    rcases ha with ⟨a', ha', rfl⟩
    exact ⟨a', ha', hxa⟩

end KernelOperator

variable {Dpo : Type u} [PartialOrder Dpo]

namespace KernelOperator

/-- Proposition 3.1.17(3): the image of a kernel operator is closed under
existing suprema. -/
theorem isSup_mem_range (K : KernelOperator Dpo) {A : Set Dpo} {s : Dpo}
    (hsub : A ⊆ Set.range K.k) (hs : IsSup A s) : s ∈ Set.range K.k := by
  have hUpper : IsUpperBound A (K.k s) := by
    intro a ha
    exact K.le_kernel_of_mem_range_le (hsub ha) (hs.1 ha)
  have hs_le : s ≤ K.k s := hs.2 (K.k s) hUpper
  have hk_le : K.k s ≤ s := K.below s
  exact ⟨s, le_antisymm hk_le hs_le⟩

end KernelOperator

instance kernelOperatorPreorder : Preorder (KernelOperator Dpo) where
  le K L := ∀ x : Dpo, K.k x ≤ L.k x
  le_refl K x := le_rfl
  le_trans K L M hKL hLM x := le_trans (hKL x) (hLM x)

/-- Proposition 3.1.17(1): the kernel operators on a dcpo form a dcpo.

The proof takes the pointwise directed supremum in the Scott-continuous function
space from Chapter 2 and verifies that it is again idempotent and below the
identity. -/
theorem kernelOperator_isDcpo (hD : IsDcpo Dpo) :
    IsDcpo (KernelOperator Dpo) := by
  classical
  intro F hF
  let G : Set (Chapter2.ScottContFun Dpo Dpo) :=
    KernelOperator.toScottContFun '' F
  have hG : DirectedSet G := by
    constructor
    · rcases hF.1 with ⟨K, hK⟩
      exact ⟨K.toScottContFun, ⟨K, hK, rfl⟩⟩
    · intro f hf g hg
      rcases hf with ⟨K, hK, rfl⟩
      rcases hg with ⟨L, hL, rfl⟩
      rcases hF.2 hK hL with ⟨M, hM, hKM, hLM⟩
      exact ⟨M.toScottContFun, ⟨M, hM, rfl⟩, hKM, hLM⟩
  rcases Chapter2.prop_2_1_18_continuous_function_space_dcpo hD G hG with ⟨g, hg⟩
  let idFun : Chapter2.ScottContFun Dpo Dpo :=
    { toFun := fun x => x, continuous := scottContinuous_id }
  have hgBelow : ∀ x : Dpo, g x ≤ x := by
    intro x
    exact hg.2 idFun (by
      intro f hf
      rcases hf with ⟨K, hK, rfl⟩
      exact K.below) x
  have hgIdem : ∀ x : Dpo, g (g x) = g x := by
    intro x
    apply le_antisymm
    · exact g.continuous.1 (hgBelow x)
    · have hEvalSup :
          IsSup ((fun f : Chapter2.ScottContFun Dpo Dpo => f x) '' G) (g x) :=
        Chapter2.scottContFun_directed_sup_apply hD hG hg x
      refine hEvalSup.2 (g (g x)) ?_
      intro y hy
      rcases hy with ⟨f, hf, rfl⟩
      rcases hf with ⟨K, hK, rfl⟩
      have hKx_le_gx : K.k x ≤ g x := hg.1 ⟨K, hK, rfl⟩ x
      have hKx_le_Kgx : K.k x ≤ K.k (g x) :=
        K.le_kernel_of_mem_range_le ⟨x, rfl⟩ hKx_le_gx
      have hKgx_le_ggx : K.k (g x) ≤ g (g x) :=
        hg.1 ⟨K, hK, rfl⟩ (g x)
      exact le_trans hKx_le_Kgx hKgx_le_ggx
  let Ksup : KernelOperator Dpo :=
    { k := g
      continuous := g.continuous
      idem := hgIdem
      below := hgBelow }
  refine ⟨Ksup, ?_⟩
  constructor
  · intro K hK x
    exact hg.1 ⟨K, hK, rfl⟩ x
  · intro L hL x
    exact hg.2 L.toScottContFun (by
      intro f hf
      rcases hf with ⟨K, hK, rfl⟩
      exact hL hK) x

/-- Proposition 3.1.17(5): kernel operators are ordered by inclusion of images. -/
theorem kernel_le_iff_range_subset (K L : KernelOperator Dpo) :
    (∀ x : Dpo, K.k x ≤ L.k x) ↔ Set.range K.k ⊆ Set.range L.k := by
  constructor
  · intro hle y hy
    have hKy : K.k y = y := (K.mem_range_iff_fixed).1 hy
    have hyL : y ≤ L.k y := by simpa [hKy] using hle y
    have hLy : L.k y ≤ y := L.below y
    have hfix : L.k y = y := le_antisymm hLy hyL
    exact ⟨y, hfix⟩
  · intro hsub x
    have hKxRange : K.k x ∈ Set.range L.k := hsub ⟨x, rfl⟩
    have hLKx : L.k (K.k x) = K.k x := (L.mem_range_iff_fixed).1 hKxRange
    calc
      K.k x = L.k (K.k x) := hLKx.symm
      _ ≤ L.k x := L.continuous.1 (K.below x)

/-- Closure operators: continuous idempotents above the identity. -/
structure ClosureOperator (D : Type u) [Preorder D] where
  c : D → D
  continuous : ScottContinuous c
  idem : ∀ x : D, c (c x) = c x
  above : ∀ x : D, x ≤ c x

namespace ClosureOperator

variable (C : ClosureOperator D)

/-- Fixed-point characterization of the image of a closure operator. -/
theorem mem_range_iff_fixed {y : D} : y ∈ Set.range C.c ↔ C.c y = y := by
  constructor
  · intro hy
    rcases hy with ⟨x, rfl⟩
    exact C.idem x
  · intro hy
    exact ⟨y, hy⟩

/-- Dual of Proposition 3.1.17(2): `c x` is the least image element above `x`. -/
theorem closure_le_of_le_mem_range {x y : D}
    (hy : y ∈ Set.range C.c) (hxy : x ≤ y) : C.c x ≤ y := by
  have hfix : C.c y = y := (C.mem_range_iff_fixed).1 hy
  calc
    C.c x ≤ C.c y := C.continuous.1 hxy
    _ = y := hfix

end ClosureOperator

end EmbeddingProjection

end Chapter3
end AbramskyJung

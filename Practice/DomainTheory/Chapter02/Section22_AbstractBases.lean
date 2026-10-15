import Practice.DomainTheory.Chapter02.Section22_Approximation

set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-!
# Abramsky--Jung, Domain Theory, Chapter 2: Section 2.2: abstract bases

Book-facing declarations are kept in source order. Reusable order-theoretic
interfaces remain in `Practice.DomainTheory.Order` and
`Practice.DomainTheory.Topology`.
-/

universe u v w

namespace AbramskyJung
namespace Chapter2

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

end Chapter2
end AbramskyJung

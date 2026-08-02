import Practice.DomainTheory.Chapter05.Section52

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 5.3

Canonicity, initiality, finality, and mixed-variance free algebra statements.

The high-level canonicity theorems are tracked as direct local proof debt.  The
current structures store domain-equation and bilimit construction data, while
the status file records which consequences have not yet been derived.
-/

universe u

namespace AbramskyJung
namespace Chapter5

open Chapter4

section ExplicitPreorderFixpoint

variable {D : Type u} [Preorder D] [OrderBot D]

/-- Iteration from bottom for a preorder presented with an explicit
antisymmetry proof.  Chapter 2's public version uses a `PartialOrder` instance;
this variant avoids changing the preorder instance stored in `OrderedDomain`. -/
def preorderBotIter (f : D → D) : Nat → D
  | 0 => ⊥
  | n + 1 => f (preorderBotIter f n)

/-- The range of the bottom iteration. -/
def preorderIterSet (f : D → D) : Set D :=
  Set.range (preorderBotIter f)

private theorem preorderBotIter_mono {f : D → D} (hf : Monotone f) :
    Monotone (preorderBotIter f) := by
  have hstep : ∀ n : Nat, preorderBotIter f n ≤ preorderBotIter f (n + 1) := by
    intro n
    induction n with
    | zero => exact bot_le
    | succ n ih => exact hf ih
  intro m n hmn
  induction hmn with
  | refl => exact le_rfl
  | step hmn ih => exact le_trans ih (hstep _)

private theorem preorderIterSet_directed {f : D → D} (hf : Monotone f) :
    Chapter3.DirectedSet (preorderIterSet f) := by
  constructor
  · exact ⟨⊥, ⟨0, rfl⟩⟩
  · intro x hx y hy
    rcases hx with ⟨m, rfl⟩
    rcases hy with ⟨n, rfl⟩
    exact ⟨preorderBotIter f (max m n), ⟨max m n, rfl⟩,
      preorderBotIter_mono hf (Nat.le_max_left m n),
      preorderBotIter_mono hf (Nat.le_max_right m n)⟩

/-- The chosen Kleene least fixed point in a dcpo whose antisymmetry is supplied
explicitly. -/
noncomputable def preorderChosenLeastFix
    (hD : Chapter3.IsDcpo D) (f : Chapter3.ContFun D D) : D :=
  Classical.choose (hD (preorderIterSet f)
    (preorderIterSet_directed f.continuous.1))

/-- Correctness and leastness of the explicit-preorder Kleene construction. -/
theorem preorderChosenLeastFix_spec
    (hD : Chapter3.IsDcpo D)
    (hanti : ∀ x y : D, x ≤ y → y ≤ x → x = y)
    (f : Chapter3.ContFun D D) :
    f (preorderChosenLeastFix hD f) = preorderChosenLeastFix hD f ∧
      ∀ y : D, f y = y → preorderChosenLeastFix hD f ≤ y := by
  let l := preorderChosenLeastFix hD f
  have hl : Chapter3.IsSup (preorderIterSet f) l :=
    Classical.choose_spec (hD (preorderIterSet f)
      (preorderIterSet_directed f.continuous.1))
  have hdir : Chapter3.DirectedSet (preorderIterSet f) :=
    preorderIterSet_directed f.continuous.1
  have hsupImage : Chapter3.IsSup (f '' preorderIterSet f) (f l) :=
    f.continuous.2 hdir hl
  have hfl_le : f l ≤ l := hsupImage.2 l (by
    intro z hz
    rcases hz with ⟨x, ⟨n, rfl⟩, rfl⟩
    exact hl.1 ⟨n + 1, rfl⟩)
  have hl_le_fl : l ≤ f l := hl.2 (f l) (by
    intro z hz
    rcases hz with ⟨n, rfl⟩
    cases n with
    | zero => exact bot_le
    | succ n =>
        exact f.continuous.1 (hl.1 ⟨n, rfl⟩))
  constructor
  · exact hanti _ _ hfl_le hl_le_fl
  · intro y hy
    apply hl.2 y
    intro z hz
    rcases hz with ⟨n, rfl⟩
    induction n with
    | zero => exact bot_le
    | succ n ih =>
        calc
          preorderBotIter f (n + 1) = f (preorderBotIter f n) := rfl
          _ ≤ f y := f.continuous.1 ih
          _ = y := hy

/-- Strict continuous commuting squares preserve the explicit-preorder Kleene
least fixed points. -/
theorem preorderChosenLeastFix_invariance
    {E : Type u} [Preorder E] [OrderBot E]
    (hD : Chapter3.IsDcpo D) (hE : Chapter3.IsDcpo E)
    (hEanti : ∀ x y : E, x ≤ y → y ≤ x → x = y)
    (f : Chapter3.ContFun D D) (g : Chapter3.ContFun E E)
    (h : Chapter3.ContFun D E) (hstrict : h ⊥ = ⊥)
    (hcomm : ∀ x : D, h (f x) = g (h x)) :
    preorderChosenLeastFix hE g = h (preorderChosenLeastFix hD f) := by
  let lD := preorderChosenLeastFix hD f
  let lE := preorderChosenLeastFix hE g
  have hsupD : Chapter3.IsSup (preorderIterSet f) lD :=
    Classical.choose_spec (hD (preorderIterSet f)
      (preorderIterSet_directed f.continuous.1))
  have hsupE : Chapter3.IsSup (preorderIterSet g) lE :=
    Classical.choose_spec (hE (preorderIterSet g)
      (preorderIterSet_directed g.continuous.1))
  have hsupImage : Chapter3.IsSup (h '' preorderIterSet f) (h lD) :=
    h.continuous.2 (preorderIterSet_directed f.continuous.1) hsupD
  have hiter : ∀ n : Nat, h (preorderBotIter f n) = preorderBotIter g n := by
    intro n
    induction n with
    | zero => exact hstrict
    | succ n ih =>
        calc
          h (preorderBotIter f (n + 1)) = h (f (preorderBotIter f n)) := rfl
          _ = g (h (preorderBotIter f n)) := hcomm _
          _ = g (preorderBotIter g n) := by rw [ih]
          _ = preorderBotIter g (n + 1) := rfl
  have himage : h '' preorderIterSet f = preorderIterSet g := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (hiter n).symm⟩
    · intro hy
      rcases hy with ⟨n, rfl⟩
      exact ⟨preorderBotIter f n, ⟨n, rfl⟩, hiter n⟩
  have hsupMapped : Chapter3.IsSup (preorderIterSet g) (h lD) := by
    rw [← himage]
    exact hsupImage
  exact hEanti _ _ (hsupE.2 _ hsupMapped.1) (hsupMapped.2 _ hsupE.1)

/-- If a continuous endofunctional on a continuous-function space preserves
bottom at a chosen source point, then its Kleene least fixed point is bottom at
that point. -/
theorem preorderChosenLeastFix_apply_eq_bot
    {X Y : Type u} [Preorder X] [Preorder Y] [OrderBot Y]
    (hYdcpo : Chapter3.IsDcpo Y)
    (hYanti : ∀ x y : Y, x ≤ y → y ≤ x → x = y)
    (phi : Chapter3.ContFun (Chapter3.ContFun X Y) (Chapter3.ContFun X Y))
    (x₀ : X)
    (hPreserves : ∀ g : Chapter3.ContFun X Y, g x₀ = ⊥ → phi g x₀ = ⊥) :
    preorderChosenLeastFix (Chapter3.ContFun.isDcpo_of_codomain hYdcpo) phi x₀ = ⊥ := by
  have hIterBottom : ∀ n : Nat, preorderBotIter phi n x₀ = ⊥ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact hPreserves _ ih
  have hIterDir : Chapter3.DirectedSet (preorderIterSet phi) :=
    preorderIterSet_directed phi.continuous.1
  have hIterSup : Chapter3.IsSup (preorderIterSet phi)
      (preorderChosenLeastFix
        (Chapter3.ContFun.isDcpo_of_codomain hYdcpo) phi) :=
    Classical.choose_spec
      ((Chapter3.ContFun.isDcpo_of_codomain hYdcpo) (preorderIterSet phi) hIterDir)
  have hEvalSup := (Chapter3.ContFun.eval_scottContinuous hYdcpo x₀).2
    hIterDir hIterSup
  apply hYanti
  · apply hEvalSup.2 ⊥
    intro y hy
    rcases hy with ⟨g, ⟨n, rfl⟩, rfl⟩
    exact le_of_eq (hIterBottom n)
  · exact bot_le

end ExplicitPreorderFixpoint

/-- Homomorphism functional `g ↦ f ∘ F g ∘ i⁻¹` from Lemma 5.3.1. -/
def algebraHomFunctional
    (F : DomainEndofunctor.{u}) (A C : FunctorAlgebra F)
    (Ainv : OrderedDomain.ContFunCarrier A.object (F.mapObj A.object))
    (g : OrderedDomain.ContFunCarrier A.object C.object) :
    OrderedDomain.ContFunCarrier A.object C.object :=
  OrderedDomain.compContFun C.structureMap
    (OrderedDomain.compContFun (F.mapHom g) Ainv)

/-- Local continuity makes the algebra-homomorphism functional Scott
continuous.  The functor image of the target is required to be a dcpo so that
directed suprema in its continuous function space are pointwise. -/
theorem algebraHomFunctional_scottContinuous
    (F : DomainEndofunctor.{u}) (hF : LocallyContinuous F)
    (A C : FunctorAlgebra F)
    (Ainv : OrderedDomain.ContFunCarrier A.object (F.mapObj A.object))
    (hFCdcpo : Chapter3.IsDcpo (F.mapObj C.object).carrier) :
    Chapter3.ScottContinuous (algebraHomFunctional F A C Ainv) := by
  let hMap := hF (D := A.object) (E := C.object)
  constructor
  · intro f g hfg x
    exact C.structureMap.continuous.1
      (hMap.1 hfg (Ainv x))
  · intro G s hG hs
    have hImageDir : Chapter3.DirectedSet
        ((fun g : OrderedDomain.ContFunCarrier A.object C.object => F.mapHom g) '' G) :=
      Chapter3.DirectedSet.image hMap.1 hG
    have hImageSup : Chapter3.IsSup
        ((fun g : OrderedDomain.ContFunCarrier A.object C.object => F.mapHom g) '' G)
        (F.mapHom s) :=
      hMap.2 hG hs
    constructor
    · intro y hy
      rcases hy with ⟨g, hg, rfl⟩
      intro x
      exact C.structureMap.continuous.1 (hMap.1 (hs.1 hg) (Ainv x))
    · intro q hq x
      have hEvalSup : Chapter3.IsSup
          ((fun k : OrderedDomain.ContFunCarrier (F.mapObj A.object) (F.mapObj C.object) =>
              k (Ainv x)) ''
            ((fun g : OrderedDomain.ContFunCarrier A.object C.object => F.mapHom g) '' G))
          (F.mapHom s (Ainv x)) :=
        (Chapter3.ContFun.eval_scottContinuous hFCdcpo (Ainv x)).2 hImageDir hImageSup
      have hEvalDir : Chapter3.DirectedSet
          ((fun k : OrderedDomain.ContFunCarrier (F.mapObj A.object) (F.mapObj C.object) =>
              k (Ainv x)) ''
            ((fun g : OrderedDomain.ContFunCarrier A.object C.object => F.mapHom g) '' G)) :=
        Chapter3.DirectedSet.image
          (Chapter3.ContFun.eval_scottContinuous hFCdcpo (Ainv x)).1 hImageDir
      have hStructSup := C.structureMap.continuous.2 hEvalDir hEvalSup
      apply hStructSup.2 (q x)
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      rcases hw with ⟨k, hk, rfl⟩
      rcases hk with ⟨g, hg, rfl⟩
      exact hq ⟨g, hg, rfl⟩ x

/-- Precomposition by a fixed continuous map is Scott-continuous on continuous
function spaces. -/
theorem precompose_scottContinuous
    (A B C : OrderedDomain.{u})
    (hCdcpo : Chapter3.IsDcpo C.carrier)
    (k : OrderedDomain.ContFunCarrier A B) :
    Chapter3.ScottContinuous
      (fun g : OrderedDomain.ContFunCarrier B C => OrderedDomain.compContFun g k) := by
  constructor
  · intro f g hfg x
    exact hfg (k x)
  · intro G s hG hs
    constructor
    · intro y hy
      rcases hy with ⟨g, hg, rfl⟩
      intro x
      exact hs.1 hg (k x)
    · intro q hq x
      have hEvalSup :=
        (Chapter3.ContFun.eval_scottContinuous hCdcpo (k x)).2 hG hs
      apply hEvalSup.2 (q x)
      intro y hy
      rcases hy with ⟨g, hg, rfl⟩
      exact hq ⟨g, hg, rfl⟩ x

/-- Postcomposition by a fixed continuous map is Scott-continuous on
continuous function spaces. -/
theorem postcompose_scottContinuous
    (A B C : OrderedDomain.{u})
    (hBdcpo : Chapter3.IsDcpo B.carrier)
    (k : OrderedDomain.ContFunCarrier B C) :
    Chapter3.ScottContinuous
      (fun g : OrderedDomain.ContFunCarrier A B =>
        OrderedDomain.compContFun k g) := by
  constructor
  · intro f g hfg x
    exact k.continuous.1 (hfg x)
  · intro G s hG hs
    constructor
    · intro y hy
      rcases hy with ⟨g, hg, rfl⟩
      intro x
      exact k.continuous.1 (hs.1 hg x)
    · intro q hq x
      have hEvalSup :=
        (Chapter3.ContFun.eval_scottContinuous hBdcpo x).2 hG hs
      have hEvalDir : Chapter3.DirectedSet
          ((fun g : OrderedDomain.ContFunCarrier A B => g x) '' G) :=
        Chapter3.DirectedSet.image
          (Chapter3.ContFun.eval_scottContinuous hBdcpo x).1 hG
      have hPostSup := k.continuous.2 hEvalDir hEvalSup
      apply hPostSup.2 (q x)
      intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      rcases hz with ⟨g, hg, rfl⟩
      exact hq ⟨g, hg, rfl⟩ x

/-- Joint composition is Scott-continuous on a product of continuous function
spaces. -/
theorem composition_scottContinuous
    (A B C : OrderedDomain.{u})
    (hBdcpo : Chapter3.IsDcpo B.carrier)
    (hCdcpo : Chapter3.IsDcpo C.carrier) :
    Chapter3.ScottContinuous
      (fun p : OrderedDomain.ContFunCarrier B C ×
          OrderedDomain.ContFunCarrier A B =>
        OrderedDomain.compContFun p.1 p.2) := by
  constructor
  · intro p q hpq x
    exact le_trans (p.1.continuous.1 ((hpq.2) x)) ((hpq.1) (q.2 x))
  · intro G s hG hs
    constructor
    · intro y hy
      rcases hy with ⟨p, hp, rfl⟩
      intro x
      exact le_trans (p.1.continuous.1 (((hs.1 hp).2) x))
        (((hs.1 hp).1) (s.2 x))
    · intro q hq x
      have hSecondEval : Chapter3.ScottContinuous
          (fun p : OrderedDomain.ContFunCarrier B C ×
              OrderedDomain.ContFunCarrier A B => p.2 x) :=
        Chapter3.ScottContinuous.comp
          (Chapter3.ContFun.eval_scottContinuous hBdcpo x)
          Chapter3.prod_snd_scottContinuous
      have hPair : Chapter3.ScottContinuous
          (fun p : OrderedDomain.ContFunCarrier B C ×
              OrderedDomain.ContFunCarrier A B => (p.1, p.2 x)) :=
        Chapter3.prod_pair_scottContinuous Chapter3.prod_fst_scottContinuous
          hSecondEval
      have hPoint : Chapter3.ScottContinuous
          (fun p : OrderedDomain.ContFunCarrier B C ×
              OrderedDomain.ContFunCarrier A B => p.1 (p.2 x)) :=
        Chapter3.ScottContinuous.comp
          (Chapter3.ContFun.apply_scottContinuous hCdcpo) hPair
      have hPointSup := hPoint.2 hG hs
      apply hPointSup.2 (q x)
      intro y hy
      rcases hy with ⟨p, hp, rfl⟩
      exact hq ⟨p, hp, rfl⟩ x

/-- The least-fixpoint clause in Lemma 5.3.1: a least algebra homomorphism is
the least fixed point of `g ↦ f ∘ F g ∘ i⁻¹` on `[A -> C]`. -/
def IsLeastFixpointOfAlgebraHomFunctional
    (F : DomainEndofunctor.{u}) (A C : FunctorAlgebra F)
    (Ainv : OrderedDomain.ContFunCarrier A.object (F.mapObj A.object))
    (h : FunctorAlgebra.Hom F A C) : Prop :=
  algebraHomFunctional F A C Ainv h.map = h.map ∧
    ∀ g : OrderedDomain.ContFunCarrier A.object C.object,
      algebraHomFunctional F A C Ainv g = g → h.map ≤ g

/-- The composition clause in Lemma 5.3.1: composing least homomorphisms through
    another algebra whose structure map is an isomorphism again gives the least
    homomorphism.  The composed homomorphism is supplied explicitly so that the
    clause is independent of bundled-map extensionality. -/
def LeastAlgebraHomCompositionProperty (F : DomainEndofunctor.{u}) : Prop :=
  ∀ (A B C : FunctorAlgebra F),
    FunctorAlgebra.StructureIso F A →
      FunctorAlgebra.StructureIso F B →
        ∀ (hBA : FunctorAlgebra.Hom F A B)
          (hCB : FunctorAlgebra.Hom F B C)
          (hCA : FunctorAlgebra.Hom F A C),
            IsLeastAlgebraHom F A B hBA →
              IsLeastAlgebraHom F B C hCB →
                hCA.map = OrderedDomain.compContFun hCB.map hBA.map →
                  IsLeastAlgebraHom F A C hCA

/-- The algebra-homomorphism functional as a bundled continuous endomap. -/
def algebraHomFunctionalContFun
    (F : DomainEndofunctor.{u}) (hF : LocallyContinuous F)
    (A C : FunctorAlgebra F) (hA : FunctorAlgebra.StructureIso F A)
    (hFCdcpo : Chapter3.IsDcpo (F.mapObj C.object).carrier) :
    Chapter3.ContFun
      (OrderedDomain.ContFunCarrier A.object C.object)
      (OrderedDomain.ContFunCarrier A.object C.object) where
  toFun := algebraHomFunctional F A C hA.inverse
  continuous := algebraHomFunctional_scottContinuous F hF A C hA.inverse hFCdcpo

/-- The map underlying the least algebra homomorphism in Lemma 5.3.1. -/
noncomputable def leastAlgebraHomMap
    (F : DomainEndofunctor.{u}) (hF : LocallyContinuous F)
    (A C : FunctorAlgebra F) (hA : FunctorAlgebra.StructureIso F A)
    (hCdcpo : Chapter3.IsDcpo C.object.carrier)
    (hFCdcpo : Chapter3.IsDcpo (F.mapObj C.object).carrier)
    [OrderBot C.object.carrier] : OrderedDomain.ContFunCarrier A.object C.object :=
  preorderChosenLeastFix (Chapter3.ContFun.isDcpo_of_codomain hCdcpo)
    (algebraHomFunctionalContFun F hF A C hA hFCdcpo)

/-- Fixed-point and leastness properties of `leastAlgebraHomMap`. -/
theorem leastAlgebraHomMap_spec
    (F : DomainEndofunctor.{u}) (hF : LocallyContinuous F)
    (A C : FunctorAlgebra F) (hA : FunctorAlgebra.StructureIso F A)
    (hCdcpo : Chapter3.IsDcpo C.object.carrier)
    (hCanti : ∀ x y : C.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFCdcpo : Chapter3.IsDcpo (F.mapObj C.object).carrier)
    [OrderBot C.object.carrier] :
    algebraHomFunctional F A C hA.inverse
        (leastAlgebraHomMap F hF A C hA hCdcpo hFCdcpo) =
      leastAlgebraHomMap F hF A C hA hCdcpo hFCdcpo ∧
    ∀ g : OrderedDomain.ContFunCarrier A.object C.object,
      algebraHomFunctional F A C hA.inverse g = g →
        leastAlgebraHomMap F hF A C hA hCdcpo hFCdcpo ≤ g := by
  have hHomAnti :
      ∀ f g : OrderedDomain.ContFunCarrier A.object C.object,
        f ≤ g → g ≤ f → f = g := by
    intro f g hfg hgf
    apply Chapter3.ContFun.ext_apply
    intro x
    exact hCanti _ _ (hfg x) (hgf x)
  exact preorderChosenLeastFix_spec
    (Chapter3.ContFun.isDcpo_of_codomain hCdcpo) hHomAnti
    (algebraHomFunctionalContFun F hF A C hA hFCdcpo)

/-- The least fixed point, bundled as an algebra homomorphism. -/
noncomputable def leastAlgebraHom
    (F : DomainEndofunctor.{u}) (hF : LocallyContinuous F)
    (A C : FunctorAlgebra F) (hA : FunctorAlgebra.StructureIso F A)
    (hCdcpo : Chapter3.IsDcpo C.object.carrier)
    (hCanti : ∀ x y : C.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFCdcpo : Chapter3.IsDcpo (F.mapObj C.object).carrier)
    [OrderBot C.object.carrier] : FunctorAlgebra.Hom F A C where
  map := leastAlgebraHomMap F hF A C hA hCdcpo hFCdcpo
  commutes := by
    intro x
    have hfix :=
      (leastAlgebraHomMap_spec F hF A C hA hCdcpo hCanti hFCdcpo).1
    have hx := congrArg (fun g => g (A.structureMap x)) hfix
    change C.structureMap
        (F.mapHom (leastAlgebraHomMap F hF A C hA hCdcpo hFCdcpo)
          (hA.inverse (A.structureMap x))) =
      leastAlgebraHomMap F hF A C hA hCdcpo hFCdcpo (A.structureMap x) at hx
    rw [hA.right_inverse x] at hx
    exact hx.symm

/-- The bundled homomorphism obtained from the functional is below every algebra
homomorphism. -/
theorem leastAlgebraHom_isLeast
    (F : DomainEndofunctor.{u}) (hF : LocallyContinuous F)
    (A C : FunctorAlgebra F) (hA : FunctorAlgebra.StructureIso F A)
    (hCdcpo : Chapter3.IsDcpo C.object.carrier)
    (hCanti : ∀ x y : C.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFCdcpo : Chapter3.IsDcpo (F.mapObj C.object).carrier)
    [OrderBot C.object.carrier] :
    IsLeastAlgebraHom F A C
      (leastAlgebraHom F hF A C hA hCdcpo hCanti hFCdcpo) := by
  intro k
  apply (leastAlgebraHomMap_spec F hF A C hA hCdcpo hCanti hFCdcpo).2 k.map
  apply Chapter3.ContFun.ext_apply
  intro x
  have hk := k.commutes (hA.inverse x)
  rw [hA.left_inverse x] at hk
  exact hk.symm

/-- Lemma 5.3.1, least mediating homomorphism component.  PDF text: for a
locally continuous functor and an isomorphism `i : F(A) -> A`, there is a least
homomorphism from `A` to every `F`-algebra.

The target carrier's dcpo and bottom hypotheses make explicit the global domain
category assumptions used in the printed fixed-point proof. -/
theorem lemma_5_3_1_canonical_fixpoint_mediating
    (F : DomainEndofunctor.{u}) (hF : LocallyContinuous F)
    (A C : FunctorAlgebra F) (hA : FunctorAlgebra.StructureIso F A)
    (hCdcpo : Chapter3.IsDcpo C.object.carrier)
    (hCanti : ∀ x y : C.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFCdcpo : Chapter3.IsDcpo (F.mapObj C.object).carrier)
    [OrderBot C.object.carrier] :
    ∃ h : FunctorAlgebra.Hom F A C, IsLeastAlgebraHom F A C h := by
  exact ⟨leastAlgebraHom F hF A C hA hCdcpo hCanti hFCdcpo,
    leastAlgebraHom_isLeast F hF A C hA hCdcpo hCanti hFCdcpo⟩

/-- Lemma 5.3.1, least-fixpoint formula component.  PDF text: the least
homomorphism is the least fixed point of `g ↦ f ∘ F(g) ∘ i⁻¹`.

The PDF supplies this as part of the recursive-domain-equation argument, but it
is not yet derived from local continuity in Lean. -/
theorem lemma_5_3_1_least_fixpoint_formula
    (F : DomainEndofunctor.{u}) (hF : LocallyContinuous F)
    (A C : FunctorAlgebra F) (hA : FunctorAlgebra.StructureIso F A)
    (hCdcpo : Chapter3.IsDcpo C.object.carrier)
    (hCanti : ∀ x y : C.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFCdcpo : Chapter3.IsDcpo (F.mapObj C.object).carrier)
    [OrderBot C.object.carrier] :
    ∃ h : FunctorAlgebra.Hom F A C,
      IsLeastAlgebraHom F A C h ∧
        IsLeastFixpointOfAlgebraHomFunctional F A C hA.inverse h := by
  let h := leastAlgebraHom F hF A C hA hCdcpo hCanti hFCdcpo
  refine ⟨h, leastAlgebraHom_isLeast F hF A C hA hCdcpo hCanti hFCdcpo, ?_⟩
  exact leastAlgebraHomMap_spec F hF A C hA hCdcpo hCanti hFCdcpo

/-- Lemma 5.3.1, composition component.  PDF text: the composition of least
homomorphisms is again least.

This is registered as local proof debt until the least-homomorphism construction
and functor laws are formalized enough to derive composition directly. -/
theorem lemma_5_3_1_least_hom_composition
    (F : DomainEndofunctor.{u}) (hF : LocallyContinuous F)
    (A B C : FunctorAlgebra F)
    (hA : FunctorAlgebra.StructureIso F A)
    (hB : FunctorAlgebra.StructureIso F B)
    (hCdcpo : Chapter3.IsDcpo C.object.carrier)
    (hCanti : ∀ x y : C.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFCdcpo : Chapter3.IsDcpo (F.mapObj C.object).carrier)
    [OrderBot C.object.carrier]
    (hBA : FunctorAlgebra.Hom F A B)
    (hCB : FunctorAlgebra.Hom F B C)
    (hCA : FunctorAlgebra.Hom F A C)
    (_hBAleast : IsLeastAlgebraHom F A B hBA)
    (hCBleast : IsLeastAlgebraHom F B C hCB)
    (hCAmap : hCA.map = OrderedDomain.compContFun hCB.map hBA.map) :
    IsLeastAlgebraHom F A C hCA := by
  let phiB := algebraHomFunctionalContFun F hF B C hB hFCdcpo
  let phiA := algebraHomFunctionalContFun F hF A C hA hFCdcpo
  let H : Chapter3.ContFun
      (OrderedDomain.ContFunCarrier B.object C.object)
      (OrderedDomain.ContFunCarrier A.object C.object) :=
    { toFun := fun g => OrderedDomain.compContFun g hBA.map
      continuous := precompose_scottContinuous A.object B.object C.object hCdcpo hBA.map }
  have hHstrict : H ⊥ = ⊥ := by
    apply Chapter3.ContFun.ext_apply
    intro x
    rfl
  have hHcomm : ∀ g : OrderedDomain.ContFunCarrier B.object C.object,
      H (phiB g) = phiA (H g) := by
    intro g
    apply Chapter3.ContFun.ext_apply
    intro x
    have hBAx : hBA.map x =
        B.structureMap (F.mapHom hBA.map (hA.inverse x)) := by
      calc
        hBA.map x = hBA.map (A.structureMap (hA.inverse x)) := by
          rw [hA.left_inverse x]
        _ = B.structureMap (F.mapHom hBA.map (hA.inverse x)) :=
          hBA.commutes (hA.inverse x)
    have hInv : hB.inverse (hBA.map x) =
        F.mapHom hBA.map (hA.inverse x) := by
      calc
        hB.inverse (hBA.map x) =
            hB.inverse (B.structureMap (F.mapHom hBA.map (hA.inverse x))) := by
              rw [hBAx]
        _ = F.mapHom hBA.map (hA.inverse x) := hB.right_inverse _
    change C.structureMap (F.mapHom g (hB.inverse (hBA.map x))) =
      C.structureMap
        (F.mapHom (OrderedDomain.compContFun g hBA.map) (hA.inverse x))
    rw [hInv]
    exact congrArg C.structureMap (F.mapHom_comp hBA.map g (hA.inverse x))
  have hHomAnti :
      ∀ f g : OrderedDomain.ContFunCarrier A.object C.object,
        f ≤ g → g ≤ f → f = g := by
    intro f g hfg hgf
    apply Chapter3.ContFun.ext_apply
    intro x
    exact hCanti _ _ (hfg x) (hgf x)
  have hFixInv :
      leastAlgebraHomMap F hF A C hA hCdcpo hFCdcpo =
        OrderedDomain.compContFun
          (leastAlgebraHomMap F hF B C hB hCdcpo hFCdcpo) hBA.map := by
    exact preorderChosenLeastFix_invariance
      (Chapter3.ContFun.isDcpo_of_codomain hCdcpo)
      (Chapter3.ContFun.isDcpo_of_codomain hCdcpo)
      hHomAnti phiB phiA H hHstrict hHcomm
  have hCB_eq : hCB.map = leastAlgebraHomMap F hF B C hB hCdcpo hFCdcpo := by
    apply Chapter3.ContFun.ext_apply
    intro x
    exact hCanti _ _
      (hCBleast (leastAlgebraHom F hF B C hB hCdcpo hCanti hFCdcpo) x)
      (leastAlgebraHom_isLeast F hF B C hB hCdcpo hCanti hFCdcpo hCB x)
  have hCA_eq : hCA.map = leastAlgebraHomMap F hF A C hA hCdcpo hFCdcpo := by
    calc
      hCA.map = OrderedDomain.compContFun hCB.map hBA.map := hCAmap
      _ = OrderedDomain.compContFun
          (leastAlgebraHomMap F hF B C hB hCdcpo hFCdcpo) hBA.map := by
            rw [hCB_eq]
      _ = leastAlgebraHomMap F hF A C hA hCdcpo hFCdcpo := hFixInv.symm
  intro k
  rw [hCA_eq]
  exact leastAlgebraHom_isLeast F hF A C hA hCdcpo hCanti hFCdcpo k

/-- Being isomorphic, as an `F`-algebra, to a canonical fixed-point package. -/
def IsCanonicalFixpoint
    (F : DomainEndofunctor.{u}) (A : FunctorAlgebra F) : Prop :=
  ∃ C : CanonicalSolution F,
    Nonempty (FunctorAlgebra.Iso F A C.solution.toAlgebra)

/-- The identity is the least endomorphism of an algebra. -/
def IdentityIsLeastEndomorphism
    (F : DomainEndofunctor.{u}) (A : FunctorAlgebra F) : Prop :=
  ∀ h : FunctorAlgebra.Hom F A A, OrderedDomain.idContFun A.object ≤ h.map

/-- The identity is the least fixed point of the homomorphism functional. -/
def IdentityIsLeastFunctionalFixpoint
    (F : DomainEndofunctor.{u}) (A : FunctorAlgebra F)
    (hA : FunctorAlgebra.StructureIso F A) : Prop :=
  algebraHomFunctional F A A hA.inverse (OrderedDomain.idContFun A.object) =
      OrderedDomain.idContFun A.object ∧
    ∀ g : OrderedDomain.ContFunCarrier A.object A.object,
      algebraHomFunctional F A A hA.inverse g = g →
        OrderedDomain.idContFun A.object ≤ g

/-- An endomap is an algebra homomorphism exactly when it is a fixed point of
the algebra-homomorphism functional. -/
theorem algebraEndomorphism_iff_functional_fixpoint
    (F : DomainEndofunctor.{u}) (A : FunctorAlgebra F)
    (hA : FunctorAlgebra.StructureIso F A)
    (g : OrderedDomain.ContFunCarrier A.object A.object) :
    (∀ x : (F.mapObj A.object).carrier,
        g (A.structureMap x) = A.structureMap (F.mapHom g x)) ↔
      algebraHomFunctional F A A hA.inverse g = g := by
  constructor
  · intro hg
    apply Chapter3.ContFun.ext_apply
    intro x
    calc
      algebraHomFunctional F A A hA.inverse g x =
          A.structureMap (F.mapHom g (hA.inverse x)) := rfl
      _ = g (A.structureMap (hA.inverse x)) := (hg (hA.inverse x)).symm
      _ = g x := by rw [hA.left_inverse]
  · intro hfix x
    have hx := congrArg (fun k => k (A.structureMap x)) hfix
    change A.structureMap (F.mapHom g (hA.inverse (A.structureMap x))) =
      g (A.structureMap x) at hx
    rw [hA.right_inverse] at hx
    exact hx.symm

/-- Clauses (2) and (3) of Theorem 5.3.2 are equivalent independently of the
canonical-chain argument. -/
theorem identityLeastEndomorphism_iff_identityLeastFunctionalFixpoint
    (F : DomainEndofunctor.{u}) (A : FunctorAlgebra F)
    (hA : FunctorAlgebra.StructureIso F A) :
    IdentityIsLeastEndomorphism F A ↔
      IdentityIsLeastFunctionalFixpoint F A hA := by
  constructor
  · intro hleast
    constructor
    · exact (algebraEndomorphism_iff_functional_fixpoint F A hA
        (OrderedDomain.idContFun A.object)).1
        (FunctorAlgebra.idHom F A).commutes
    · intro g hg
      let k : FunctorAlgebra.Hom F A A :=
        { map := g
          commutes :=
            (algebraEndomorphism_iff_functional_fixpoint F A hA g).2 hg }
      exact hleast k
  · intro hleast k
    exact hleast.2 k.map
      ((algebraEndomorphism_iff_functional_fixpoint F A hA k.map).1 k.commutes)

/-- The bilimit approximation equations imply that the identity on a canonical
solution is below every algebra endomorphism.  This is the core induction in
the proof of Theorem 5.3.2. -/
theorem canonicalIdentityIsLeastEndomorphism
    (F : DomainEndofunctor.{u}) (C : CanonicalSolution F) :
    IdentityIsLeastEndomorphism F C.solution.toAlgebra := by
  letI : OrderBot C.construction.base.carrier := C.construction.base_orderBot
  letI : OrderBot C.solution.object.carrier := C.construction.solution_orderBot
  intro h
  apply C.construction.identity_is_sup_stage_approximations.2 h.map
  intro q hq
  rcases hq with ⟨n, rfl⟩
  have hstage : ∀ m : Nat,
      epApproximationContFun (C.construction.stagePair m) ≤ h.map := by
    intro m
    induction m with
    | zero =>
        intro x
        calc
          epApproximationContFun (C.construction.stagePair 0) x =
              (C.construction.stagePair 0).e
                ((C.construction.stagePair 0).p x) := rfl
          _ = (C.construction.stagePair 0).e
              (⊥ : C.construction.base.carrier) := by
                congr 1
                exact C.construction.base_subsingleton
                  ((C.construction.stagePair 0).p x)
                  (⊥ : C.construction.base.carrier)
          _ = ⊥ := C.construction.stage_zero_strict
          _ ≤ h.map x := bot_le
    | succ m ih =>
        intro x
        have hp :
            (C.construction.stagePair (m + 1)).p x =
              F.mapHom
                (epProjectionContFun (C.construction.stagePair m))
                (C.solution.unfold x) := by
          calc
            (C.construction.stagePair (m + 1)).p x =
                (C.construction.stagePair (m + 1)).p
                  (C.solution.fold (C.solution.unfold x)) := by
                    rw [C.solution.fold_unfold]
            _ = F.mapHom
                (epProjectionContFun (C.construction.stagePair m))
                (C.solution.unfold x) :=
              C.construction.fold_stage_projection m (C.solution.unfold x)
        have he : ∀ y :
            (FunctorIterationObject F C.construction.base (m + 1)).carrier,
            (C.construction.stagePair (m + 1)).e y =
              C.solution.fold
                (F.mapHom (epEmbeddingContFun (C.construction.stagePair m)) y) := by
          intro y
          calc
            (C.construction.stagePair (m + 1)).e y =
                C.solution.fold
                  (C.solution.unfold ((C.construction.stagePair (m + 1)).e y)) :=
              (C.solution.fold_unfold _).symm
            _ = C.solution.fold
                (F.mapHom (epEmbeddingContFun (C.construction.stagePair m)) y) := by
              rw [C.construction.unfold_stage_embedding]
        calc
          epApproximationContFun (C.construction.stagePair (m + 1)) x =
              (C.construction.stagePair (m + 1)).e
                ((C.construction.stagePair (m + 1)).p x) := rfl
          _ = C.solution.fold
              (F.mapHom (epEmbeddingContFun (C.construction.stagePair m))
                ((C.construction.stagePair (m + 1)).p x)) := he _
          _ = C.solution.fold
              (F.mapHom (epEmbeddingContFun (C.construction.stagePair m))
                (F.mapHom (epProjectionContFun (C.construction.stagePair m))
                  (C.solution.unfold x))) := by rw [hp]
          _ = C.solution.fold
              (F.mapHom
                (OrderedDomain.compContFun
                  (epEmbeddingContFun (C.construction.stagePair m))
                  (epProjectionContFun (C.construction.stagePair m)))
                (C.solution.unfold x)) := by
                  rw [F.mapHom_comp]
          _ = C.solution.fold
              (F.mapHom (epApproximationContFun (C.construction.stagePair m))
                (C.solution.unfold x)) := rfl
          _ ≤ h.map x := by
            have hmono :
                C.solution.fold
                    (F.mapHom (epApproximationContFun
                      (C.construction.stagePair m)) (C.solution.unfold x)) ≤
                  C.solution.fold (F.mapHom h.map (C.solution.unfold x)) :=
              C.solution.fold.continuous.1
                ((C.construction.locallyContinuous).1 ih (C.solution.unfold x))
            have hcomm := h.commutes (C.solution.unfold x)
            change h.map (C.solution.fold (C.solution.unfold x)) =
              C.solution.fold (F.mapHom h.map (C.solution.unfold x)) at hcomm
            have heq : C.solution.fold (F.mapHom h.map (C.solution.unfold x)) =
                h.map x := by
              calc
                C.solution.fold (F.mapHom h.map (C.solution.unfold x)) =
                    h.map (C.solution.fold (C.solution.unfold x)) := hcomm.symm
                _ = h.map x := by rw [C.solution.fold_unfold]
            exact le_trans hmono (le_of_eq heq)
  exact hstage n

/-- Leastness of the identity transports across an algebra isomorphism. -/
theorem identityLeastEndomorphism_of_algebraIso
    (F : DomainEndofunctor.{u}) {A B : FunctorAlgebra F}
    (i : FunctorAlgebra.Iso F A B)
    (hB : IdentityIsLeastEndomorphism F B) :
    IdentityIsLeastEndomorphism F A := by
  intro k x
  let conjugate : FunctorAlgebra.Hom F B B :=
    FunctorAlgebra.compHom F i.hom
      (FunctorAlgebra.compHom F k i.inv)
  have hb := hB conjugate (i.hom.map x)
  have hinv := i.inv.map.continuous.1 hb
  calc
    x = i.inv.map (i.hom.map x) := (i.inv_hom_id x).symm
    _ ≤ i.inv.map (conjugate.map (i.hom.map x)) := hinv
    _ = i.inv.map (i.hom.map (k.map (i.inv.map (i.hom.map x)))) := rfl
    _ = k.map (i.inv.map (i.hom.map x)) := i.inv_hom_id _
    _ = k.map x := by rw [i.inv_hom_id]

/-- If the identity is the least fixed point of the algebra functional, every
strict algebra endomorphism is the identity. -/
theorem identityOnlyBottomStrictEndomorphism_of_leastFunctionalFixpoint
    (F : DomainEndofunctor.{u}) (hF : LocallyContinuous F)
    (A : FunctorAlgebra F) (hA : FunctorAlgebra.StructureIso F A)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hAanti : ∀ x y : A.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFAdcpo : Chapter3.IsDcpo (F.mapObj A.object).carrier)
    [OrderBot A.object.carrier]
    (hLeast : IdentityIsLeastFunctionalFixpoint F A hA) :
    ∀ k : FunctorAlgebra.Hom F A A,
      Chapter2.StrictMap k.map →
        k.map = OrderedDomain.idContFun A.object := by
  intro k hk
  let phi := algebraHomFunctionalContFun F hF A A hA hFAdcpo
  let H : Chapter3.ContFun
      (OrderedDomain.ContFunCarrier A.object A.object)
      (OrderedDomain.ContFunCarrier A.object A.object) :=
    { toFun := fun g => OrderedDomain.compContFun k.map g
      continuous := postcompose_scottContinuous A.object A.object A.object
        hAdcpo k.map }
  have hHstrict : H ⊥ = ⊥ := by
    apply Chapter3.ContFun.ext_apply
    intro x
    exact hk
  have hHcomm : ∀ g : OrderedDomain.ContFunCarrier A.object A.object,
      H (phi g) = phi (H g) := by
    intro g
    apply Chapter3.ContFun.ext_apply
    intro x
    change k.map (A.structureMap (F.mapHom g (hA.inverse x))) =
      A.structureMap
        (F.mapHom (OrderedDomain.compContFun k.map g) (hA.inverse x))
    calc
      k.map (A.structureMap (F.mapHom g (hA.inverse x))) =
          A.structureMap (F.mapHom k.map (F.mapHom g (hA.inverse x))) :=
        k.commutes (F.mapHom g (hA.inverse x))
      _ = A.structureMap
          (F.mapHom (OrderedDomain.compContFun k.map g) (hA.inverse x)) := by
        rw [F.mapHom_comp]
  have hHomAnti :
      ∀ f g : OrderedDomain.ContFunCarrier A.object A.object,
        f ≤ g → g ≤ f → f = g := by
    intro f g hfg hgf
    apply Chapter3.ContFun.ext_apply
    intro x
    exact hAanti _ _ (hfg x) (hgf x)
  have hspec := leastAlgebraHomMap_spec F hF A A hA hAdcpo hAanti hFAdcpo
  have hLeastEq :
      leastAlgebraHomMap F hF A A hA hAdcpo hFAdcpo =
        OrderedDomain.idContFun A.object := by
    apply Chapter3.ContFun.ext_apply
    intro x
    exact hAanti _ _
      (hspec.2 (OrderedDomain.idContFun A.object) hLeast.1 x)
      (hLeast.2 (leastAlgebraHomMap F hF A A hA hAdcpo hFAdcpo) hspec.1 x)
  have hinvariance := preorderChosenLeastFix_invariance
    (Chapter3.ContFun.isDcpo_of_codomain hAdcpo)
    (Chapter3.ContFun.isDcpo_of_codomain hAdcpo)
    hHomAnti phi phi H hHstrict hHcomm
  change leastAlgebraHomMap F hF A A hA hAdcpo hFAdcpo =
    H (leastAlgebraHomMap F hF A A hA hAdcpo hFAdcpo) at hinvariance
  rw [hLeastEq] at hinvariance
  apply Chapter3.ContFun.ext_apply
  intro x
  have hx := congrArg (fun g => g x) hinvariance
  exact hx.symm

/-- Uniqueness of strict endomorphisms yields an algebra isomorphism from the
given fixed point to the chosen canonical one. -/
theorem algebraIsoCanonical_of_identityOnlyStrict
    (F : DomainEndofunctor.{u}) (hF : LocallyContinuous F)
    (C : CanonicalSolution F)
    (A : FunctorAlgebra F) (hA : FunctorAlgebra.StructureIso F A)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hAanti : ∀ x y : A.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFAdcpo : Chapter3.IsDcpo (F.mapObj A.object).carrier)
    [OrderBot A.object.carrier]
    (hStrict : ∀ k : FunctorAlgebra.Hom F A A,
      Chapter2.StrictMap k.map → k.map = OrderedDomain.idContFun A.object) :
    Nonempty (FunctorAlgebra.Iso F A C.solution.toAlgebra) := by
  let CAlg := C.solution.toAlgebra
  letI : OrderBot CAlg.object.carrier := C.construction.solution_orderBot
  let hC : FunctorAlgebra.StructureIso F CAlg :=
    { inverse := C.solution.unfold
      left_inverse := C.solution.fold_unfold
      right_inverse := C.solution.unfold_fold }
  let toC : FunctorAlgebra.Hom F A CAlg :=
    leastAlgebraHom F hF A CAlg hA C.construction.solution_dcpo
      C.construction.solution_antisymm C.construction.functor_solution_dcpo
  let fromC : FunctorAlgebra.Hom F CAlg A :=
    leastAlgebraHom F hF CAlg A hC hAdcpo hAanti hFAdcpo
  have hToLeast : IsLeastAlgebraHom F A CAlg toC :=
    leastAlgebraHom_isLeast F hF A CAlg hA C.construction.solution_dcpo
      C.construction.solution_antisymm C.construction.functor_solution_dcpo
  have hFromLeast : IsLeastAlgebraHom F CAlg A fromC :=
    leastAlgebraHom_isLeast F hF CAlg A hC hAdcpo hAanti hFAdcpo
  let endA : FunctorAlgebra.Hom F A A := FunctorAlgebra.compHom F fromC toC
  let endC : FunctorAlgebra.Hom F CAlg CAlg := FunctorAlgebra.compHom F toC fromC
  have hEndALeast : IsLeastAlgebraHom F A A endA :=
    lemma_5_3_1_least_hom_composition F hF A CAlg A hA hC
      hAdcpo hAanti hFAdcpo toC fromC endA hToLeast hFromLeast rfl
  have hEndCLeast : IsLeastAlgebraHom F CAlg CAlg endC :=
    lemma_5_3_1_least_hom_composition F hF CAlg A CAlg hC hA
      C.construction.solution_dcpo C.construction.solution_antisymm
      C.construction.functor_solution_dcpo fromC toC endC hFromLeast hToLeast rfl
  have hEndAStrict : Chapter2.StrictMap endA.map := by
    exact hAanti _ _
      (hEndALeast (FunctorAlgebra.idHom F A) ⊥) bot_le
  have hEndAeq : endA.map = OrderedDomain.idContFun A.object :=
    hStrict endA hEndAStrict
  have hCanonicalLeast := canonicalIdentityIsLeastEndomorphism F C
  have hEndCeq : endC.map = OrderedDomain.idContFun C.solution.object := by
    apply Chapter3.ContFun.ext_apply
    intro x
    exact C.construction.solution_antisymm _ _
      (hEndCLeast (FunctorAlgebra.idHom F CAlg) x)
      (hCanonicalLeast endC x)
  exact ⟨
    { hom := toC
      inv := fromC
      hom_inv_id := by
        intro x
        have hx := congrArg (fun f => f x) hEndCeq
        exact hx
      inv_hom_id := by
        intro x
        have hx := congrArg (fun f => f x) hEndAeq
        exact hx }⟩

/-- The identity is the only endomorphism satisfying an externally supplied strictness predicate. -/
def IdentityOnlyStrictEndomorphism
    (F : DomainEndofunctor.{u}) (A : FunctorAlgebra F)
    (Strict : OrderedDomain.ContFunCarrier A.object A.object → Prop) : Prop :=
  ∀ h : FunctorAlgebra.Hom F A A,
    Strict h.map → h.map = OrderedDomain.idContFun A.object

/-- The PDF's bottom-preserving strict-endomorphism specialization. -/
def IdentityOnlyBottomStrictEndomorphism
    (F : DomainEndofunctor.{u}) (A : FunctorAlgebra F) [OrderBot A.object.carrier] :
    Prop :=
  IdentityOnlyStrictEndomorphism F A (fun f => Chapter2.StrictMap f)

/-- Theorem 5.3.2, invariance part 1.  PDF text: for a locally continuous
functor and an isomorphism `i : F(A) -> A`, the canonical-fixpoint condition,
least-endomorphism condition, least fixed point of `φ`, and uniqueness of strict
endomorphisms are equivalent.

Here strictness means preservation of the globally assumed bottom element.  The
dcpo hypothesis is explicit because the local `OrderedDomain` bundle currently
contains only the carrier and preorder. -/
theorem theorem_5_3_2_invariance_part1
    (F : DomainEndofunctor.{u}) (hF : LocallyContinuous F)
    (C : CanonicalSolution F)
    (A : FunctorAlgebra F) (hA : FunctorAlgebra.StructureIso F A)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hAanti : ∀ x y : A.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFAdcpo : Chapter3.IsDcpo (F.mapObj A.object).carrier)
    [OrderBot A.object.carrier] :
    (IsCanonicalFixpoint F A ↔ IdentityIsLeastEndomorphism F A) ∧
      (IdentityIsLeastEndomorphism F A ↔
        IdentityIsLeastFunctionalFixpoint F A hA) ∧
      (IdentityIsLeastFunctionalFixpoint F A hA ↔
        IdentityOnlyBottomStrictEndomorphism F A) := by
  have h1to2 : IsCanonicalFixpoint F A → IdentityIsLeastEndomorphism F A := by
    rintro ⟨C', ⟨i⟩⟩
    exact identityLeastEndomorphism_of_algebraIso F i
      (canonicalIdentityIsLeastEndomorphism F C')
  have h2iff3 :=
    identityLeastEndomorphism_iff_identityLeastFunctionalFixpoint F A hA
  have h3to4 : IdentityIsLeastFunctionalFixpoint F A hA →
      IdentityOnlyBottomStrictEndomorphism F A := by
    intro h3
    exact identityOnlyBottomStrictEndomorphism_of_leastFunctionalFixpoint
      F hF A hA hAdcpo hAanti hFAdcpo h3
  have h4to1 : IdentityOnlyBottomStrictEndomorphism F A →
      IsCanonicalFixpoint F A := by
    intro h4
    exact ⟨C, algebraIsoCanonical_of_identityOnlyStrict
      F hF C A hA hAdcpo hAanti hFAdcpo h4⟩
  refine ⟨?_, h2iff3, ?_⟩
  · constructor
    · exact h1to2
    · intro h2
      exact h4to1 (h3to4 (h2iff3.1 h2))
  · constructor
    · exact h3to4
    · intro h4
      exact h2iff3.1 (h1to2 (h4to1 h4))

/-- Compatibility name for the bottom-strict statement of Theorem 5.3.2. -/
theorem theorem_5_3_2_invariance_part1_bottom_strict
    (F : DomainEndofunctor.{u}) (hF : LocallyContinuous F)
    (C : CanonicalSolution F)
    (A : FunctorAlgebra F) (hA : FunctorAlgebra.StructureIso F A)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hAanti : ∀ x y : A.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFAdcpo : Chapter3.IsDcpo (F.mapObj A.object).carrier)
    [OrderBot A.object.carrier] :
    (IsCanonicalFixpoint F A ↔ IdentityIsLeastEndomorphism F A) ∧
      (IdentityIsLeastEndomorphism F A ↔
        IdentityIsLeastFunctionalFixpoint F A hA) ∧
      (IdentityIsLeastFunctionalFixpoint F A hA ↔
        IdentityOnlyBottomStrictEndomorphism F A) := by
  exact theorem_5_3_2_invariance_part1 F hF C A hA hAdcpo hAanti hFAdcpo

/-- Theorem 5.3.3.  PDF text: the canonical fixpoint of a locally continuous
functor is a sub-domain of every other fixpoint.

The conclusion remains local proof debt until it is derived from the stored
functor-iteration bilimit construction. -/
theorem theorem_5_3_3_minimality_part1
    (F : DomainEndofunctor.{u}) (_hF : LocallyContinuous F)
    (C : CanonicalSolution F) (S : DomainEquationSolution F) :
    Nonempty (SubdomainOf C.solution.object S.object) := by
  admit

/-- A locally continuous endofunctor on the category whose morphisms are strict
continuous maps.  Bottom structures are explicit because `OrderedDomain`
deliberately stores only a preorder. -/
structure StrictLocallyContinuous (F : DomainEndofunctor.{u}) : Prop where
  locallyContinuous : LocallyContinuous F
  mapHom_strict :
    ∀ ⦃D E : OrderedDomain.{u}⦄
      (Dbot : OrderBot D.carrier) (Ebot : OrderBot E.carrier)
      (FDbot : OrderBot (F.mapObj D).carrier)
      (FEbot : OrderBot (F.mapObj E).carrier)
      (f : OrderedDomain.ContFunCarrier D E),
      @Chapter2.StrictMap D.carrier E.carrier inferInstance inferInstance
          Dbot Ebot f →
        @Chapter2.StrictMap (F.mapObj D).carrier (F.mapObj E).carrier
          inferInstance inferInstance FDbot FEbot (F.mapHom f)

/-- An `F`-algebra in the strict-functions setting used by Theorem 5.3.4.
The dcpo fields recover the ambient domain-category assumptions absent from the
lightweight `OrderedDomain` carrier. -/
structure StrictFunctorAlgebra (F : DomainEndofunctor.{u}) where
  algebra : FunctorAlgebra F
  source_bot : OrderBot (F.mapObj algebra.object).carrier
  target_bot : OrderBot algebra.object.carrier
  object_dcpo : Chapter3.IsDcpo algebra.object.carrier
  object_antisymm :
    ∀ x y : algebra.object.carrier, x ≤ y → y ≤ x → x = y
  functor_object_dcpo : Chapter3.IsDcpo (F.mapObj algebra.object).carrier
  structure_strict :
    @Chapter2.StrictMap (F.mapObj algebra.object).carrier algebra.object.carrier
      inferInstance inferInstance source_bot target_bot algebra.structureMap

/-- Strict homomorphisms between strict `F`-algebras. -/
structure StrictAlgebraHom
    (F : DomainEndofunctor.{u}) (A B : StrictFunctorAlgebra F) where
  hom : FunctorAlgebra.Hom F A.algebra B.algebra
  strict :
    @Chapter2.StrictMap A.algebra.object.carrier B.algebra.object.carrier
      inferInstance inferInstance A.target_bot B.target_bot hom.map

/-- Initiality in the category of strict `F`-algebras and strict
homomorphisms. -/
def IsStrictInitialAlgebra
    (F : DomainEndofunctor.{u}) (A : StrictFunctorAlgebra F) : Prop :=
  ∀ B : StrictFunctorAlgebra F,
    ∃ h : StrictAlgebraHom F A B,
      ∀ k : StrictAlgebraHom F A B, k.hom.map = h.hom.map

/-- A canonical solution in the strict-map category.  Strictness of the
Lambek isomorphism is construction data, not an initiality conclusion. -/
structure StrictCanonicalSolution (F : DomainEndofunctor.{u}) where
  canonical : CanonicalSolution F
  functor_solution_orderBot :
    OrderBot (F.mapObj canonical.solution.object).carrier
  fold_strict :
    @Chapter2.StrictMap
      (F.mapObj canonical.solution.object).carrier canonical.solution.object.carrier
      inferInstance inferInstance functor_solution_orderBot
      canonical.construction.solution_orderBot canonical.solution.fold
  unfold_strict :
    @Chapter2.StrictMap
      canonical.solution.object.carrier (F.mapObj canonical.solution.object).carrier
      inferInstance inferInstance canonical.construction.solution_orderBot
      functor_solution_orderBot canonical.solution.unfold

/-- The strict initiality assertion for the canonical fold algebra in
Theorem 5.3.4. -/
def IsStrictInitialFold
    (F : DomainEndofunctor.{u}) (C : CanonicalSolution F) : Prop :=
  ∃ A : StrictFunctorAlgebra F,
    A.algebra = C.solution.toAlgebra ∧ IsStrictInitialAlgebra F A

/-- Theorem 5.3.4, strict-functions form.  PDF text: for the canonical solution
`D` of `X ≅ F(X)`, `fold : F(D) -> D` is an initial `F`-algebra in the
category of strict functions. -/
theorem theorem_5_3_4_initiality_strict
    (F : DomainEndofunctor.{u}) (hF : StrictLocallyContinuous F)
    (C : StrictCanonicalSolution F) :
    IsStrictInitialFold F C.canonical := by
  letI cBot : OrderBot C.canonical.solution.object.carrier :=
    C.canonical.construction.solution_orderBot
  letI fcBot : OrderBot (F.mapObj C.canonical.solution.object).carrier :=
    C.functor_solution_orderBot
  let canonicalAlgebra : StrictFunctorAlgebra F :=
    { algebra := C.canonical.solution.toAlgebra
      source_bot := C.functor_solution_orderBot
      target_bot := C.canonical.construction.solution_orderBot
      object_dcpo := C.canonical.construction.solution_dcpo
      object_antisymm := C.canonical.construction.solution_antisymm
      functor_object_dcpo := C.canonical.construction.functor_solution_dcpo
      structure_strict := C.fold_strict }
  letI canonicalBot : OrderBot canonicalAlgebra.algebra.object.carrier :=
    canonicalAlgebra.target_bot
  letI functorCanonicalBot :
      OrderBot (F.mapObj canonicalAlgebra.algebra.object).carrier :=
    canonicalAlgebra.source_bot
  refine ⟨canonicalAlgebra, rfl, ?_⟩
  intro B
  letI bBot : OrderBot B.algebra.object.carrier := B.target_bot
  letI fbBot : OrderBot (F.mapObj B.algebra.object).carrier := B.source_bot
  let hCanonicalIso : FunctorAlgebra.StructureIso F canonicalAlgebra.algebra :=
    { inverse := C.canonical.solution.unfold
      left_inverse := C.canonical.solution.fold_unfold
      right_inverse := C.canonical.solution.unfold_fold }
  let leastHom : FunctorAlgebra.Hom F canonicalAlgebra.algebra B.algebra :=
    leastAlgebraHom F hF.locallyContinuous canonicalAlgebra.algebra B.algebra
      hCanonicalIso B.object_dcpo B.object_antisymm B.functor_object_dcpo
  have hFunctionalPreservesBottom :
      ∀ g : OrderedDomain.ContFunCarrier
          canonicalAlgebra.algebra.object B.algebra.object,
        g (⊥ : canonicalAlgebra.algebra.object.carrier) = ⊥ →
          algebraHomFunctional F canonicalAlgebra.algebra B.algebra
            hCanonicalIso.inverse g
              (⊥ : canonicalAlgebra.algebra.object.carrier) = ⊥ := by
    intro g hg
    change B.algebra.structureMap
      (F.mapHom g (C.canonical.solution.unfold ⊥)) = ⊥
    rw [C.unfold_strict]
    have hFg := hF.mapHom_strict canonicalBot bBot
      functorCanonicalBot fbBot g hg
    change F.mapHom g (@Bot.bot _ functorCanonicalBot.toBot) =
      @Bot.bot _ fbBot.toBot at hFg
    change B.algebra.structureMap
      (F.mapHom g (@Bot.bot _ functorCanonicalBot.toBot)) =
        @Bot.bot _ bBot.toBot
    exact Eq.trans (congrArg B.algebra.structureMap hFg) B.structure_strict
  have hLeastStrict :
      @Chapter2.StrictMap canonicalAlgebra.algebra.object.carrier
        B.algebra.object.carrier inferInstance inferInstance
        canonicalAlgebra.target_bot B.target_bot leastHom.map := by
    exact preorderChosenLeastFix_apply_eq_bot B.object_dcpo B.object_antisymm
      (algebraHomFunctionalContFun F hF.locallyContinuous
        canonicalAlgebra.algebra B.algebra hCanonicalIso B.functor_object_dcpo)
      (⊥ : canonicalAlgebra.algebra.object.carrier) hFunctionalPreservesBottom
  let initialHom : StrictAlgebraHom F canonicalAlgebra B :=
    { hom := leastHom
      strict := hLeastStrict }
  refine ⟨initialHom, ?_⟩
  intro k
  let phiCanonical := algebraHomFunctionalContFun F hF.locallyContinuous
    canonicalAlgebra.algebra canonicalAlgebra.algebra hCanonicalIso
      canonicalAlgebra.functor_object_dcpo
  let phiTarget := algebraHomFunctionalContFun F hF.locallyContinuous
    canonicalAlgebra.algebra B.algebra hCanonicalIso B.functor_object_dcpo
  let postcompose : Chapter3.ContFun
      (OrderedDomain.ContFunCarrier canonicalAlgebra.algebra.object
        canonicalAlgebra.algebra.object)
      (OrderedDomain.ContFunCarrier canonicalAlgebra.algebra.object
        B.algebra.object) :=
    { toFun := fun g => OrderedDomain.compContFun k.hom.map g
      continuous := postcompose_scottContinuous
        canonicalAlgebra.algebra.object canonicalAlgebra.algebra.object
          B.algebra.object canonicalAlgebra.object_dcpo k.hom.map }
  have hPostStrict : postcompose ⊥ = ⊥ := by
    apply Chapter3.ContFun.ext_apply
    intro x
    exact k.strict
  have hPostComm : ∀ g : OrderedDomain.ContFunCarrier
      canonicalAlgebra.algebra.object canonicalAlgebra.algebra.object,
      postcompose (phiCanonical g) = phiTarget (postcompose g) := by
    intro g
    apply Chapter3.ContFun.ext_apply
    intro x
    change k.hom.map
        (C.canonical.solution.fold
          (F.mapHom g (C.canonical.solution.unfold x))) =
      B.algebra.structureMap
        (F.mapHom (OrderedDomain.compContFun k.hom.map g)
          (C.canonical.solution.unfold x))
    calc
      k.hom.map
          (C.canonical.solution.fold
            (F.mapHom g (C.canonical.solution.unfold x))) =
        B.algebra.structureMap
          (F.mapHom k.hom.map
            (F.mapHom g (C.canonical.solution.unfold x))) :=
        k.hom.commutes _
      _ = B.algebra.structureMap
          (F.mapHom (OrderedDomain.compContFun k.hom.map g)
            (C.canonical.solution.unfold x)) := by rw [F.mapHom_comp]
  have hCanonicalMapAnti : ∀ f g : OrderedDomain.ContFunCarrier
      canonicalAlgebra.algebra.object canonicalAlgebra.algebra.object,
      f ≤ g → g ≤ f → f = g := by
    intro f g hfg hgf
    apply Chapter3.ContFun.ext_apply
    intro x
    exact canonicalAlgebra.object_antisymm _ _ (hfg x) (hgf x)
  have hTargetMapAnti : ∀ f g : OrderedDomain.ContFunCarrier
      canonicalAlgebra.algebra.object B.algebra.object,
      f ≤ g → g ≤ f → f = g := by
    intro f g hfg hgf
    apply Chapter3.ContFun.ext_apply
    intro x
    exact B.object_antisymm _ _ (hfg x) (hgf x)
  let leastEnd := leastAlgebraHom F hF.locallyContinuous
    canonicalAlgebra.algebra canonicalAlgebra.algebra hCanonicalIso
      canonicalAlgebra.object_dcpo canonicalAlgebra.object_antisymm
        canonicalAlgebra.functor_object_dcpo
  have hLeastEndEq : leastEnd.map =
      OrderedDomain.idContFun canonicalAlgebra.algebra.object := by
    have hLeastEnd := leastAlgebraHom_isLeast F hF.locallyContinuous
      canonicalAlgebra.algebra canonicalAlgebra.algebra hCanonicalIso
        canonicalAlgebra.object_dcpo canonicalAlgebra.object_antisymm
          canonicalAlgebra.functor_object_dcpo
    have hIdentityLeast := canonicalIdentityIsLeastEndomorphism F C.canonical
    apply Chapter3.ContFun.ext_apply
    intro x
    exact canonicalAlgebra.object_antisymm _ _
      ((hLeastEnd (FunctorAlgebra.idHom F canonicalAlgebra.algebra)) x)
      ((hIdentityLeast leastEnd) x)
  have hInvariant := preorderChosenLeastFix_invariance
    (Chapter3.ContFun.isDcpo_of_codomain canonicalAlgebra.object_dcpo)
    (Chapter3.ContFun.isDcpo_of_codomain B.object_dcpo)
    hTargetMapAnti phiCanonical phiTarget postcompose hPostStrict hPostComm
  change leastHom.map = postcompose leastEnd.map at hInvariant
  rw [hLeastEndEq] at hInvariant
  apply Chapter3.ContFun.ext_apply
  intro x
  have hx := congrArg (fun g => g x) hInvariant
  exact hx.symm

/-- Whiskering a continuous map on both sides is Scott-continuous on the
corresponding continuous function space. -/
theorem whisker_scottContinuous
    (A X Y B : OrderedDomain.{u})
    (hYdcpo : Chapter3.IsDcpo Y.carrier)
    (pre : OrderedDomain.ContFunCarrier A X)
    (post : OrderedDomain.ContFunCarrier Y B) :
    Chapter3.ScottContinuous
      (fun q : OrderedDomain.ContFunCarrier X Y =>
        OrderedDomain.compContFun post (OrderedDomain.compContFun q pre)) := by
  constructor
  · intro f g hfg x
    exact post.continuous.1 (hfg (pre x))
  · intro G s hG hs
    constructor
    · intro y hy
      rcases hy with ⟨g, hg, rfl⟩
      intro x
      exact post.continuous.1 (hs.1 hg (pre x))
    · intro q hq x
      have hEvalSup :=
        (Chapter3.ContFun.eval_scottContinuous hYdcpo (pre x)).2 hG hs
      have hEvalDir : Chapter3.DirectedSet
          ((fun g : OrderedDomain.ContFunCarrier X Y => g (pre x)) '' G) :=
        Chapter3.DirectedSet.image
          (Chapter3.ContFun.eval_scottContinuous hYdcpo (pre x)).1 hG
      have hPostSup := post.continuous.2 hEvalDir hEvalSup
      apply hPostSup.2 (q x)
      intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      rcases hz with ⟨g, hg, rfl⟩
      exact hq ⟨g, hg, rfl⟩ x

/-- The coalgebra-morphism functional `g ↦ fold ∘ F(g) ∘ destruct`. -/
def coalgebraHomFunctional
    (F : DomainEndofunctor.{u})
    (B : FunctorCoalgebra F) (C : DomainEquationSolution F)
    (g : OrderedDomain.ContFunCarrier B.object C.object) :
    OrderedDomain.ContFunCarrier B.object C.object :=
  OrderedDomain.compContFun C.fold
    (OrderedDomain.compContFun (F.mapHom g) B.destruct)

/-- Local continuity makes the coalgebra-morphism functional
Scott-continuous. -/
theorem coalgebraHomFunctional_scottContinuous
    (F : DomainEndofunctor.{u}) (hF : LocallyContinuous F)
    (B : FunctorCoalgebra F) (C : DomainEquationSolution F)
    (hFCdcpo : Chapter3.IsDcpo (F.mapObj C.object).carrier) :
    Chapter3.ScottContinuous (coalgebraHomFunctional F B C) := by
  change Chapter3.ScottContinuous
    (fun g => OrderedDomain.compContFun C.fold
      (OrderedDomain.compContFun (F.mapHom g) B.destruct))
  exact Chapter3.ScottContinuous.comp
    (f := fun q : OrderedDomain.ContFunCarrier
        (F.mapObj B.object) (F.mapObj C.object) =>
      OrderedDomain.compContFun C.fold
        (OrderedDomain.compContFun q B.destruct))
    (g := fun g : OrderedDomain.ContFunCarrier B.object C.object => F.mapHom g)
    (whisker_scottContinuous B.object (F.mapObj B.object)
      (F.mapObj C.object) C.object hFCdcpo B.destruct C.fold)
    (hF (D := B.object) (E := C.object))

/-- Bundle the coalgebra-morphism functional as a continuous endomap. -/
def coalgebraHomFunctionalContFun
    (F : DomainEndofunctor.{u}) (hF : LocallyContinuous F)
    (B : FunctorCoalgebra F) (C : DomainEquationSolution F)
    (hFCdcpo : Chapter3.IsDcpo (F.mapObj C.object).carrier) :
    Chapter3.ContFun
      (OrderedDomain.ContFunCarrier B.object C.object)
      (OrderedDomain.ContFunCarrier B.object C.object) where
  toFun := coalgebraHomFunctional F B C
  continuous := coalgebraHomFunctional_scottContinuous F hF B C hFCdcpo

/-- Theorem 5.3.5.  For a locally continuous functor with canonical fixpoint
`D = FIX(F)`, `unfold : D -> F(D)` is a final coalgebra. -/
theorem theorem_5_3_5_finality
    (F : DomainEndofunctor.{u}) (hF : LocallyContinuous F)
    (C : CanonicalSolution F) :
    IsFinalCoalgebra F C.solution.toCoalgebra := by
  intro B
  letI cBot : OrderBot C.solution.object.carrier :=
    C.construction.solution_orderBot
  let phi := coalgebraHomFunctionalContFun F hF B C.solution
    C.construction.functor_solution_dcpo
  let mediator : OrderedDomain.ContFunCarrier B.object C.solution.object :=
    preorderChosenLeastFix
      (Chapter3.ContFun.isDcpo_of_codomain C.construction.solution_dcpo) phi
  have hMapAnti : ∀ f g : OrderedDomain.ContFunCarrier B.object C.solution.object,
      f ≤ g → g ≤ f → f = g := by
    intro f g hfg hgf
    apply Chapter3.ContFun.ext_apply
    intro x
    exact C.construction.solution_antisymm _ _ (hfg x) (hgf x)
  have hMediatorFix : phi mediator = mediator :=
    (preorderChosenLeastFix_spec
      (Chapter3.ContFun.isDcpo_of_codomain C.construction.solution_dcpo)
      hMapAnti phi).1
  have hMediatorCommutes : ∀ x : B.object.carrier,
      C.solution.unfold (mediator x) = F.mapHom mediator (B.destruct x) := by
    intro x
    have hx := congrArg (fun g => C.solution.unfold (g x)) hMediatorFix
    change C.solution.unfold
        (C.solution.fold (F.mapHom mediator (B.destruct x))) =
      C.solution.unfold (mediator x) at hx
    rw [C.solution.unfold_fold] at hx
    exact hx.symm
  refine ⟨mediator, hMediatorCommutes, ?_⟩
  intro k hk
  have hStage : ∀ n : Nat, ∀ x : B.object.carrier,
      (C.construction.stagePair n).p (mediator x) =
        (C.construction.stagePair n).p (k x) := by
    intro n
    induction n with
    | zero =>
        intro x
        exact C.construction.base_subsingleton _ _
    | succ n ih =>
        intro x
        let pn : OrderedDomain.ContFunCarrier C.solution.object
            (FunctorIterationObject F C.construction.base n) :=
          epProjectionContFun (C.construction.stagePair n)
        have hMaps : OrderedDomain.compContFun pn mediator =
            OrderedDomain.compContFun pn k := by
          apply Chapter3.ContFun.ext_apply
          exact ih
        have hProjectionFromMediator :
            (C.construction.stagePair (n + 1)).p (mediator x) =
              (show (FunctorIterationObject F C.construction.base (n + 1)).carrier
                from F.mapHom pn (C.solution.unfold (mediator x))) := by
          calc
            (C.construction.stagePair (n + 1)).p (mediator x) =
                (C.construction.stagePair (n + 1)).p
                  (C.solution.fold (C.solution.unfold (mediator x))) := by
                    rw [C.solution.fold_unfold]
            _ = F.mapHom pn (C.solution.unfold (mediator x)) := by
                  simpa [pn] using
                    C.construction.fold_stage_projection n
                      (C.solution.unfold (mediator x))
        have hMiddleRaw :
            F.mapHom pn (C.solution.unfold (mediator x)) =
              F.mapHom pn (C.solution.unfold (k x)) := by
          calc
            F.mapHom pn (C.solution.unfold (mediator x)) =
                F.mapHom pn (F.mapHom mediator (B.destruct x)) := by
                  rw [hMediatorCommutes x]
            _ = F.mapHom (OrderedDomain.compContFun pn mediator)
                  (B.destruct x) := by rw [F.mapHom_comp]
            _ = F.mapHom (OrderedDomain.compContFun pn k)
                  (B.destruct x) := by rw [hMaps]
            _ = F.mapHom pn (F.mapHom k (B.destruct x)) := by
                  exact (F.mapHom_comp k pn (B.destruct x)).symm
            _ = F.mapHom pn (C.solution.unfold (k x)) := by
                  exact congrArg (F.mapHom pn) (hk x).symm
        have hMiddle :
            (show (FunctorIterationObject F C.construction.base (n + 1)).carrier
              from F.mapHom pn (C.solution.unfold (mediator x))) =
            (show (FunctorIterationObject F C.construction.base (n + 1)).carrier
              from F.mapHom pn (C.solution.unfold (k x))) := hMiddleRaw
        have hProjectionToK :
            (show (FunctorIterationObject F C.construction.base (n + 1)).carrier
              from F.mapHom pn (C.solution.unfold (k x))) =
              (C.construction.stagePair (n + 1)).p (k x) :=
          Eq.trans
            (by simpa [pn] using
              (C.construction.fold_stage_projection n
                (C.solution.unfold (k x))).symm)
            (congrArg (C.construction.stagePair (n + 1)).p
              (C.solution.fold_unfold (k x)))
        exact Eq.trans hProjectionFromMediator (Eq.trans hMiddle hProjectionToK)
  apply Chapter3.ContFun.ext_apply
  intro x
  have hApproxEq : ∀ n : Nat,
      epApproximationContFun (C.construction.stagePair n) (mediator x) =
        epApproximationContFun (C.construction.stagePair n) (k x) := by
    intro n
    exact congrArg (C.construction.stagePair n).e (hStage n x)
  have hEvalMediator :=
    (Chapter3.ContFun.eval_scottContinuous C.construction.solution_dcpo
      (mediator x)).2 C.construction.stage_approximations_directed
        C.construction.identity_is_sup_stage_approximations
  have hMediatorLe : mediator x ≤ k x := by
    apply hEvalMediator.2 (k x)
    intro y hy
    rcases hy with ⟨a, ⟨n, rfl⟩, rfl⟩
    change epApproximationContFun (C.construction.stagePair n) (mediator x) ≤ k x
    rw [hApproxEq n]
    exact C.construction.identity_is_sup_stage_approximations.1 ⟨n, rfl⟩ (k x)
  have hEvalK :=
    (Chapter3.ContFun.eval_scottContinuous C.construction.solution_dcpo
      (k x)).2 C.construction.stage_approximations_directed
        C.construction.identity_is_sup_stage_approximations
  have hKLe : k x ≤ mediator x := by
    apply hEvalK.2 (mediator x)
    intro y hy
    rcases hy with ⟨a, ⟨n, rfl⟩, rfl⟩
    change epApproximationContFun (C.construction.stagePair n) (k x) ≤ mediator x
    rw [← hApproxEq n]
    exact C.construction.identity_is_sup_stage_approximations.1 ⟨n, rfl⟩
      (mediator x)
  exact C.construction.solution_antisymm _ _ hKLe hMediatorLe


end Chapter5
end AbramskyJung

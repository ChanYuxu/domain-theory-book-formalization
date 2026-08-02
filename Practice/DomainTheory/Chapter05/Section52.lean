import Practice.DomainTheory.Chapter05.Section51

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 5.2

Continuous functors, local continuity, mixed variance, and parameterized
canonical solutions.

Several numbered results in this file use lightweight colimit or mixed-variant
interfaces rather than the full categorical constructions from the PDF.  See
`formalization_status.md` for the item-by-item semantic-strength audit.
-/

universe u

namespace AbramskyJung
namespace Chapter5

open Chapter4

/-- A bundled embedding-projection pair between ordered domains. -/
structure DomainEmbedding (D E : OrderedDomain.{u}) where
  pair : Chapter3.EPPair D.carrier E.carrier

namespace DomainEmbedding

/-- The embedding component as a bundled continuous map. -/
def embedding {D E : OrderedDomain.{u}} (e : DomainEmbedding D E) :
    OrderedDomain.ContFunCarrier D E where
  toFun := e.pair.e
  continuous := e.pair.continuous_e

/-- The projection component as a bundled continuous map. -/
def projection {D E : OrderedDomain.{u}} (e : DomainEmbedding D E) :
    OrderedDomain.ContFunCarrier E D where
  toFun := e.pair.p
  continuous := e.pair.continuous_p

end DomainEmbedding

/-- Compatibility of a cocone over an expanding approximation chain. -/
def ExpandingCoconeCompatible (S : ApproximationChain.{u})
    {L : OrderedDomain.{u}}
    (coconeMap : ∀ n : Nat, OrderedDomain.ContFunCarrier (S.object n) L) : Prop :=
  ∀ n : Nat, ∀ x : (S.object n).carrier,
    coconeMap (n + 1) ((S.step n).e x) = coconeMap n x

/-- The concrete universal property of a colimit of an expanding chain. -/
structure IsExpandingColimit (S : ApproximationChain.{u})
    (L : OrderedDomain.{u})
    (coconeMap : ∀ n : Nat, OrderedDomain.ContFunCarrier (S.object n) L) : Prop where
  compatible : ExpandingCoconeCompatible S coconeMap
  desc :
    ∀ (X : OrderedDomain.{u})
      (targetCocone : ∀ n : Nat, OrderedDomain.ContFunCarrier (S.object n) X),
      ExpandingCoconeCompatible S targetCocone →
        ∃! mediating : OrderedDomain.ContFunCarrier L X,
          ∀ n : Nat, ∀ x : (S.object n).carrier,
            mediating (coconeMap n x) = targetCocone n x

/-- A cocone claimed to be the colimit of an expanding approximation chain. -/
structure ExpandingColimit (S : ApproximationChain.{u}) where
  object : OrderedDomain.{u}
  coconeMap : ∀ n : Nat, OrderedDomain.ContFunCarrier (S.object n) object
  isColimit : Prop
  isColimit_iff : isColimit ↔ IsExpandingColimit S object coconeMap

/-- Compatibility of a cocone over the image of an expanding chain. -/
def FunctorImageCoconeCompatible
    (F : DomainEndofunctor.{u}) (S : ApproximationChain.{u})
    {X : OrderedDomain.{u}}
    (coconeMap : ∀ n : Nat,
      OrderedDomain.ContFunCarrier (F.mapObj (S.object n)) X) : Prop :=
  ∀ n : Nat, ∀ x : (F.mapObj (S.object n)).carrier,
    coconeMap (n + 1)
        (F.mapHom (DomainEmbedding.embedding { pair := S.step n }) x) =
      coconeMap n x

/-- The universal property of the image cocone obtained by applying a functor
to an expanding colimit. -/
structure IsFunctorImageColimit
    (F : DomainEndofunctor.{u}) (S : ApproximationChain.{u})
    (L : ExpandingColimit S)
    (coconeMap : ∀ n : Nat,
      OrderedDomain.ContFunCarrier (F.mapObj (S.object n)) (F.mapObj L.object)) : Prop where
  source_colimit : L.isColimit
  map_eq : ∀ n : Nat, coconeMap n = F.mapHom (L.coconeMap n)
  compatible : FunctorImageCoconeCompatible F S coconeMap
  desc :
    ∀ (X : OrderedDomain.{u})
      (targetCocone : ∀ n : Nat,
        OrderedDomain.ContFunCarrier (F.mapObj (S.object n)) X),
      FunctorImageCoconeCompatible F S targetCocone →
        ∃! mediating : OrderedDomain.ContFunCarrier (F.mapObj L.object) X,
          ∀ n : Nat, ∀ x : (F.mapObj (S.object n)).carrier,
            mediating (coconeMap n x) = targetCocone n x

/-- The image cocone obtained by applying a domain endofunctor to a colimit
cocone, bundled with its universal property. -/
structure FunctorImageColimit
    (F : DomainEndofunctor.{u}) (S : ApproximationChain.{u})
    (L : ExpandingColimit S) where
  coconeMap : ∀ n : Nat,
    OrderedDomain.ContFunCarrier (F.mapObj (S.object n)) (F.mapObj L.object)
  isColimit : IsFunctorImageColimit F S L coconeMap

/-- Definition 5.2.1: continuous functors preserve colimits of expanding
sequences. -/
structure ContinuousDomainFunctor (F : DomainEndofunctor.{u}) : Prop where
  preserves_expanding_colimits :
    ∀ (S : ApproximationChain.{u}) (L : ExpandingColimit S),
      L.isColimit →
        IsFunctorImageColimit F S L (fun n => F.mapHom (L.coconeMap n))

/-- An initial embedding from which the canonical chain is generated.  This is an
e-p-pair, matching the embedding used in Lemma 5.2.2. -/
structure InitialEmbedding (F : DomainEndofunctor.{u}) where
  base : OrderedDomain.{u}
  embedding : DomainEmbedding base (F.mapObj base)

namespace InitialEmbedding

/-- The embedding component `A -> F(A)`. -/
def embed {F : DomainEndofunctor.{u}} (e : InitialEmbedding F) :
    OrderedDomain.ContFunCarrier e.base (F.mapObj e.base) :=
  DomainEmbedding.embedding e.embedding

/-- The projection/upper-adjoint component `F(A) -> A`. -/
def projection {F : DomainEndofunctor.{u}} (e : InitialEmbedding F) :
    OrderedDomain.ContFunCarrier (F.mapObj e.base) e.base :=
  DomainEmbedding.projection e.embedding

end InitialEmbedding

/-- The iterated chain `A -> F A -> F (F A) -> ...` used in Lemma 5.2.2.  It
records the source chain data only; existence of the fold/unfold solution is the
separate conclusion of Lemma 5.2.2. -/
structure CanonicalFunctorChain (F : DomainEndofunctor.{u})
    (e : InitialEmbedding F) where
  chain : ApproximationChain.{u}
  starts_at_base : chain.object 0 = e.base
  succ_is_functor_image : ∀ n : Nat, chain.object (n + 1) = F.mapObj (chain.object n)

/-- The two mediating maps produced by the shifted-chain argument in Lemma
5.2.2, together with their equations on the two colimit cocones.  The global
inverse laws are deliberately not fields: they follow from colimit uniqueness. -/
structure CanonicalChainColimitComparison
    (F : DomainEndofunctor.{u})
    {e : InitialEmbedding F} (C : CanonicalFunctorChain F e)
    (L : ExpandingColimit C.chain) where
  fold : OrderedDomain.ContFunCarrier (F.mapObj L.object) L.object
  unfold : OrderedDomain.ContFunCarrier L.object (F.mapObj L.object)
  fold_unfold_on_cocone :
    ∀ (n : Nat) (x : (C.chain.object n).carrier),
      fold (unfold (L.coconeMap n x)) = L.coconeMap n x
  unfold_fold_on_image_cocone :
    ∀ (n : Nat) (x : (F.mapObj (C.chain.object n)).carrier),
      unfold (fold (F.mapHom (L.coconeMap n) x)) =
        F.mapHom (L.coconeMap n) x

/-- Lemma 5.2.2.  PDF text: for a continuous functor and an embedding
`e : A -> F(A)`, the colimit of `A -> F(A) -> F(F(A)) -> ...` gives
`D ≅ F(D)` by explicit `fold` and `unfold` maps satisfying the displayed
equations.

The stage equations are the concrete formulas from the shifted-chain
construction; the proof below derives the global inverse laws solely by the
two colimit universal properties. -/
theorem lemma_5_2_2_continuous_functor_canonical_chain
    (F : DomainEndofunctor.{u}) (hF : ContinuousDomainFunctor F)
    (e : InitialEmbedding F) (C : CanonicalFunctorChain F e)
    (L : ExpandingColimit C.chain) (hL : L.isColimit)
    (M : CanonicalChainColimitComparison F C L) :
    ∃ sol : DomainEquationSolution F, sol.object = L.object := by
  have hSourceColimit : IsExpandingColimit C.chain L.object L.coconeMap :=
    L.isColimit_iff.mp hL
  let foldUnfold : OrderedDomain.ContFunCarrier L.object L.object :=
    OrderedDomain.compContFun M.fold M.unfold
  have hFoldUnfoldStages :
      ∀ n : Nat, ∀ x : (C.chain.object n).carrier,
        foldUnfold (L.coconeMap n x) = L.coconeMap n x :=
    M.fold_unfold_on_cocone
  rcases hSourceColimit.desc L.object L.coconeMap hSourceColimit.compatible with
    ⟨sourceMediator, hSourceMediator, hSourceUnique⟩
  have hFoldUnfoldMediator : foldUnfold = sourceMediator := by
    exact hSourceUnique foldUnfold hFoldUnfoldStages
  have hIdentityMediator : OrderedDomain.idContFun L.object = sourceMediator := by
    apply hSourceUnique
    intro n x
    rfl
  have hFoldUnfold : foldUnfold = OrderedDomain.idContFun L.object :=
    Eq.trans hFoldUnfoldMediator hIdentityMediator.symm
  have hImageColimit := hF.preserves_expanding_colimits C.chain L hL
  let unfoldFold : OrderedDomain.ContFunCarrier
      (F.mapObj L.object) (F.mapObj L.object) :=
    OrderedDomain.compContFun M.unfold M.fold
  have hUnfoldFoldStages :
      ∀ n : Nat, ∀ x : (F.mapObj (C.chain.object n)).carrier,
        unfoldFold (F.mapHom (L.coconeMap n) x) =
          F.mapHom (L.coconeMap n) x :=
    M.unfold_fold_on_image_cocone
  rcases hImageColimit.desc (F.mapObj L.object)
      (fun n => F.mapHom (L.coconeMap n)) hImageColimit.compatible with
    ⟨imageMediator, hImageMediator, hImageUnique⟩
  have hUnfoldFoldMediator : unfoldFold = imageMediator := by
    exact hImageUnique unfoldFold hUnfoldFoldStages
  have hImageIdentityMediator : OrderedDomain.idContFun (F.mapObj L.object) =
      imageMediator := by
    apply hImageUnique
    intro n x
    rfl
  have hUnfoldFold : unfoldFold = OrderedDomain.idContFun (F.mapObj L.object) :=
    Eq.trans hUnfoldFoldMediator hImageIdentityMediator.symm
  let sol : DomainEquationSolution F :=
    { object := L.object
      fold := M.fold
      unfold := M.unfold
      fold_unfold := by
        intro x
        have hx := congrArg (fun f => f x) hFoldUnfold
        exact hx
      unfold_fold := by
        intro x
        have hx := congrArg (fun f => f x) hUnfoldFold
        exact hx }
  exact ⟨sol, rfl⟩

/-- Definition 5.2.3: locally continuous functors on categories of domains. -/
abbrev def_5_2_3_locally_continuous_functor (F : DomainEndofunctor.{u}) : Prop :=
  LocallyContinuous F

/-- Proposition 5.2.4: a locally continuous functor restricts to a continuous
functor on the corresponding categories of embeddings.

The book states this proposition without proof.  The exact image-colimit
universal property is represented above, so this remains an explicit omitted
proof rather than a proof of a weaker wrapper. -/
theorem prop_5_2_4_locally_continuous_restricts_to_hom_continuity
    (F : DomainEndofunctor.{u}) (_hF : LocallyContinuous F) :
    ContinuousDomainFunctor F := by
  admit

/-- A binary covariant functor on the bundled domain interface. -/
structure BinaryDomainFunctor where
  mapObj : OrderedDomain.{u} → OrderedDomain.{u} → OrderedDomain.{u}
  mapHom :
    ∀ ⦃D₁ D₂ E₁ E₂ : OrderedDomain.{u}⦄,
      OrderedDomain.ContFunCarrier D₁ D₂ →
        OrderedDomain.ContFunCarrier E₁ E₂ →
          OrderedDomain.ContFunCarrier (mapObj D₁ E₁) (mapObj D₂ E₂)
  mapHom_id :
    ∀ ⦃D E : OrderedDomain.{u}⦄ (x : (mapObj D E).carrier),
      mapHom (OrderedDomain.idContFun D) (OrderedDomain.idContFun E) x = x
  mapHom_comp :
    ∀ ⦃D₁ D₂ D₃ E₁ E₂ E₃ : OrderedDomain.{u}⦄
      (f₁ : OrderedDomain.ContFunCarrier D₁ D₂)
      (f₂ : OrderedDomain.ContFunCarrier D₂ D₃)
      (g₁ : OrderedDomain.ContFunCarrier E₁ E₂)
      (g₂ : OrderedDomain.ContFunCarrier E₂ E₃)
      (x : (mapObj D₁ E₁).carrier),
        mapHom f₂ g₂ (mapHom f₁ g₁ x) =
          mapHom (OrderedDomain.compContFun f₂ f₁)
            (OrderedDomain.compContFun g₂ g₁) x
  mapHom_congr :
    ∀ ⦃D₁ D₂ E₁ E₂ : OrderedDomain.{u}⦄
      {f f' : OrderedDomain.ContFunCarrier D₁ D₂}
      {g g' : OrderedDomain.ContFunCarrier E₁ E₂},
      (∀ x : D₁.carrier, f x = f' x) →
        (∀ y : E₁.carrier, g y = g' y) →
          ∀ z : (mapObj D₁ E₁).carrier, mapHom f g z = mapHom f' g' z

/-- Freeze the first coordinate of a binary functor to get an endofunctor. -/
def BinaryDomainFunctor.fixedEndofunctor
    (F : BinaryDomainFunctor.{u}) (D : OrderedDomain.{u}) :
    DomainEndofunctor.{u} where
  mapObj := fun E => F.mapObj D E
  mapHom := fun {_E₁ _E₂} f => F.mapHom (OrderedDomain.idContFun D) f
  mapHom_id := fun {_E} x => F.mapHom_id x
  mapHom_comp := by
    intro E₁ E₂ E₃ f g x
    calc
      F.mapHom (OrderedDomain.idContFun D) g
          (F.mapHom (OrderedDomain.idContFun D) f x) =
          F.mapHom
            (OrderedDomain.compContFun (OrderedDomain.idContFun D)
              (OrderedDomain.idContFun D))
            (OrderedDomain.compContFun g f) x :=
        F.mapHom_comp (OrderedDomain.idContFun D) (OrderedDomain.idContFun D) f g x
      _ = F.mapHom (OrderedDomain.idContFun D)
          (OrderedDomain.compContFun g f) x := by
        apply F.mapHom_congr
        · intro y
          rfl
        · intro y
          rfl
  mapHom_congr := by
    intro E₁ E₂ f g hfg x
    exact F.mapHom_congr (fun y => rfl) hfg x

/-- A functorial choice of canonical fixed points for a parameterized equation:
on objects it sends `D` to the object of the chosen solution of
`X = F(D, X)`. -/
structure ParameterizedFixFunctor (F : BinaryDomainFunctor.{u}) where
  mapObj : OrderedDomain.{u} → OrderedDomain.{u}
  solution : ∀ D : OrderedDomain.{u}, DomainEquationSolution (F.fixedEndofunctor D)
  mapObj_eq_solution : ∀ D : OrderedDomain.{u}, mapObj D = (solution D).object
  mapHom :
    ∀ ⦃D E : OrderedDomain.{u}⦄,
      OrderedDomain.ContFunCarrier D E →
        OrderedDomain.ContFunCarrier (mapObj D) (mapObj E)
  locallyContinuous : Prop
  locallyContinuous_iff :
    locallyContinuous ↔
      ∀ ⦃D E : OrderedDomain.{u}⦄,
        Chapter3.ScottContinuous
          (fun f : OrderedDomain.ContFunCarrier D E => mapHom f)

/-- Local continuity for binary covariant functors.  The parameterized
fixed-point construction is the conclusion of Proposition 5.2.7 and is not
stored in this hypothesis. -/
structure LocallyContinuousBinary (F : BinaryDomainFunctor.{u}) : Prop where
  hom_continuous :
    ∀ ⦃D₁ D₂ E₁ E₂ : OrderedDomain.{u}⦄,
      Chapter3.ScottContinuous
        (fun p :
            OrderedDomain.ContFunCarrier D₁ D₂ ×
              OrderedDomain.ContFunCarrier E₁ E₂ =>
          F.mapHom p.1 p.2)

/-- A mixed-variance functor, contravariant in the first coordinate and covariant in the second. -/
structure MixedVariantFunctor where
  mapObj : OrderedDomain.{u} → OrderedDomain.{u} → OrderedDomain.{u}
  mapHom :
    ∀ ⦃D₁ D₂ E₁ E₂ : OrderedDomain.{u}⦄,
      OrderedDomain.ContFunCarrier D₂ D₁ →
        OrderedDomain.ContFunCarrier E₁ E₂ →
          OrderedDomain.ContFunCarrier (mapObj D₁ E₁) (mapObj D₂ E₂)
  mapHom_id :
    ∀ ⦃D E : OrderedDomain.{u}⦄,
      ∀ x : (mapObj D E).carrier,
        mapHom (OrderedDomain.idContFun D) (OrderedDomain.idContFun E) x = x
  mapHom_comp :
    ∀ ⦃D₁ D₂ D₃ E₁ E₂ E₃ : OrderedDomain.{u}⦄
      (f₁ : OrderedDomain.ContFunCarrier D₂ D₁)
      (f₂ : OrderedDomain.ContFunCarrier D₃ D₂)
      (g₁ : OrderedDomain.ContFunCarrier E₁ E₂)
      (g₂ : OrderedDomain.ContFunCarrier E₂ E₃)
      (x : (mapObj D₁ E₁).carrier),
        mapHom f₂ g₂ (mapHom f₁ g₁ x) =
          mapHom (OrderedDomain.compContFun f₁ f₂)
            (OrderedDomain.compContFun g₂ g₁) x
  mapHom_congr :
    ∀ ⦃D₁ D₂ E₁ E₂ : OrderedDomain.{u}⦄
      {f f' : OrderedDomain.ContFunCarrier D₂ D₁}
      {g g' : OrderedDomain.ContFunCarrier E₁ E₂},
      (∀ x : D₂.carrier, f x = f' x) →
        (∀ y : E₁.carrier, g y = g' y) →
          ∀ z : (mapObj D₁ E₁).carrier, mapHom f g z = mapHom f' g' z

/-- The product of two directed hom-sets used in Definition 5.2.5. -/
def MixedVariantHomProductSet
    {D₁ D₂ E₁ E₂ : OrderedDomain.{u}}
    (A : Set (OrderedDomain.ContFunCarrier D₂ D₁))
    (A' : Set (OrderedDomain.ContFunCarrier E₁ E₂)) :
    Set (OrderedDomain.ContFunCarrier D₂ D₁ × OrderedDomain.ContFunCarrier E₁ E₂) :=
  {p | p.1 ∈ A ∧ p.2 ∈ A'}

/-- The set `{ F(f, f') | f in A, f' in A' }` from the displayed
Definition 5.2.5 supremum equation. -/
def MixedVariantHomImageSet
    (F : MixedVariantFunctor.{u})
    {D₁ D₂ E₁ E₂ : OrderedDomain.{u}}
    (A : Set (OrderedDomain.ContFunCarrier D₂ D₁))
    (A' : Set (OrderedDomain.ContFunCarrier E₁ E₂)) :
    Set (OrderedDomain.ContFunCarrier (F.mapObj D₁ E₁) (F.mapObj D₂ E₂)) :=
  (fun p : OrderedDomain.ContFunCarrier D₂ D₁ ×
      OrderedDomain.ContFunCarrier E₁ E₂ => F.mapHom p.1 p.2) ''
    MixedVariantHomProductSet A A'

/-- Definition 5.2.5, PDF-shaped local-continuity equation: for directed
hom-sets `A` and `A'`, `F (sup A, sup A')` is the supremum of all
`F(f, f')` with `f in A` and `f' in A'`. -/
def MixedVariantDirectedSupContinuity (F : MixedVariantFunctor.{u}) : Prop :=
  ∀ ⦃D₁ D₂ E₁ E₂ : OrderedDomain.{u}⦄
    (A : Set (OrderedDomain.ContFunCarrier D₂ D₁))
    (A' : Set (OrderedDomain.ContFunCarrier E₁ E₂))
    (fSup : OrderedDomain.ContFunCarrier D₂ D₁)
    (gSup : OrderedDomain.ContFunCarrier E₁ E₂),
      Chapter3.DirectedSet A →
        Chapter3.DirectedSet A' →
          Chapter3.IsSup A fSup →
            Chapter3.IsSup A' gSup →
              Chapter3.IsSup (MixedVariantHomImageSet F A A') (F.mapHom fSup gSup)

/-- Product-hom Scott continuity implies the displayed directed-supremum
equation in Definition 5.2.5. -/
theorem mixedVariantDirectedSupContinuity_of_scottContinuous
    (F : MixedVariantFunctor.{u})
    (hF :
      ∀ ⦃D₁ D₂ E₁ E₂ : OrderedDomain.{u}⦄,
        Chapter3.ScottContinuous
          (fun p :
              OrderedDomain.ContFunCarrier D₂ D₁ ×
                OrderedDomain.ContFunCarrier E₁ E₂ =>
            F.mapHom p.1 p.2)) :
    MixedVariantDirectedSupContinuity F := by
  intro D₁ D₂ E₁ E₂ A A' fSup gSup hA hA' hfSup hgSup
  let P : Set (OrderedDomain.ContFunCarrier D₂ D₁ ×
      OrderedDomain.ContFunCarrier E₁ E₂) :=
    MixedVariantHomProductSet A A'
  have hPdir : Chapter3.DirectedSet P := by
    rcases hA.1 with ⟨f₀, hf₀⟩
    rcases hA'.1 with ⟨g₀, hg₀⟩
    constructor
    · exact ⟨(f₀, g₀), hf₀, hg₀⟩
    · intro x hx y hy
      rcases hA.2 hx.1 hy.1 with ⟨f, hf, hxf, hyf⟩
      rcases hA'.2 hx.2 hy.2 with ⟨g, hg, hxg, hyg⟩
      exact ⟨(f, g), ⟨hf, hg⟩, ⟨hxf, hxg⟩, ⟨hyf, hyg⟩⟩
  have hPsup : Chapter3.IsSup P (fSup, gSup) := by
    rcases hA.1 with ⟨f₀, hf₀⟩
    rcases hA'.1 with ⟨g₀, hg₀⟩
    constructor
    · intro p hp
      exact ⟨hfSup.1 hp.1, hgSup.1 hp.2⟩
    · intro y hy
      constructor
      · apply hfSup.2
        intro f hf
        exact (hy (a := (f, g₀)) ⟨hf, hg₀⟩).1
      · apply hgSup.2
        intro g hg
        exact (hy (a := (f₀, g)) ⟨hf₀, hg⟩).2
  exact (hF (D₁ := D₁) (D₂ := D₂) (E₁ := E₁) (E₂ := E₂)).2 hPdir hPsup

/-- Definition 5.2.5 proper: local continuity for a mixed-variance functor,
recording both the hom-poset Scott-continuity package and the displayed
directed-supremum equation from the PDF. -/
structure def_5_2_5_mixed_variant_locally_continuous
    (F : MixedVariantFunctor.{u}) : Prop where
  hom_continuous :
    ∀ ⦃D₁ D₂ E₁ E₂ : OrderedDomain.{u}⦄,
      Chapter3.ScottContinuous
        (fun p :
            OrderedDomain.ContFunCarrier D₂ D₁ ×
              OrderedDomain.ContFunCarrier E₁ E₂ =>
          F.mapHom p.1 p.2)
  directed_sup_continuity : MixedVariantDirectedSupContinuity F

/-- A solution of the mixed-variance equation `D = F(D,D)`. -/
structure MixedDomainEquationSolution (F : MixedVariantFunctor.{u}) where
  object : OrderedDomain.{u}
  fold : OrderedDomain.ContFunCarrier (F.mapObj object object) object
  unfold : OrderedDomain.ContFunCarrier object (F.mapObj object object)
  fold_unfold : ∀ x : object.carrier, fold (unfold x) = x
  unfold_fold : ∀ x : (F.mapObj object object).carrier, unfold (fold x) = x

/-- The paired object sequence used to solve a mixed-variance equation.

At each successor stage the contravariant and covariant arguments exchange
roles.  Keeping both components explicit avoids treating `D ↦ F(D,D)` as a
covariant endofunctor, which it is not. -/
def MixedFunctorObjectPair
    (F : MixedVariantFunctor.{u}) (A B : OrderedDomain.{u}) :
    Nat → OrderedDomain.{u} × OrderedDomain.{u}
  | 0 => (A, B)
  | n + 1 =>
      let P := MixedFunctorObjectPair F A B n
      (F.mapObj P.2 P.1, F.mapObj P.1 P.2)

/-- The left component of the mixed functor iteration. -/
abbrev MixedFunctorLeftObject
    (F : MixedVariantFunctor.{u}) (A B : OrderedDomain.{u}) (n : Nat) :
    OrderedDomain.{u} :=
  (MixedFunctorObjectPair F A B n).1

/-- The right component of the mixed functor iteration. -/
abbrev MixedFunctorRightObject
    (F : MixedVariantFunctor.{u}) (A B : OrderedDomain.{u}) (n : Nat) :
    OrderedDomain.{u} :=
  (MixedFunctorObjectPair F A B n).2

/-- A pair of maps satisfying the mixed-variance commuting diagrams. -/
structure MixedHomPair
    (F : MixedVariantFunctor.{u})
    (A B : MixedDomainEquationSolution F) where
  forward : OrderedDomain.ContFunCarrier A.object B.object
  backward : OrderedDomain.ContFunCarrier B.object A.object
  forward_commutes :
    ∀ x : (F.mapObj A.object A.object).carrier,
      forward (A.fold x) = B.fold (F.mapHom backward forward x)
  backward_commutes :
    ∀ y : (F.mapObj B.object B.object).carrier,
      backward (B.fold y) = A.fold (F.mapHom forward backward y)

/-- An isomorphism between two mixed recursive-equation solutions. -/
structure MixedSolutionIso
    (F : MixedVariantFunctor.{u})
    (A B : MixedDomainEquationSolution F) where
  homPair : MixedHomPair F A B
  forward_backward_id :
    ∀ y : B.object.carrier, homPair.forward (homPair.backward y) = y
  backward_forward_id :
    ∀ x : A.object.carrier, homPair.backward (homPair.forward x) = x

/-- Leastness for mixed homomorphism pairs. -/
def IsLeastMixedHomPair
    (F : MixedVariantFunctor.{u})
    (A B : MixedDomainEquationSolution F)
    (p : MixedHomPair F A B) : Prop :=
  ∀ q : MixedHomPair F A B, p.forward ≤ q.forward ∧ p.backward ≤ q.backward

/-- Composition clause from Lemma 5.3.6: composing least mixed hom-pairs gives
another least mixed hom-pair.  Because the local mixed-variant functor interface
does not derive the composed pair automatically, the composed pair is supplied
with its two component maps identified. -/
def LeastMixedHomPairCompositionProperty (F : MixedVariantFunctor.{u}) : Prop :=
  ∀ A B C : MixedDomainEquationSolution F,
    ∀ (pAB : MixedHomPair F A B)
      (pBC : MixedHomPair F B C)
      (pAC : MixedHomPair F A C),
      IsLeastMixedHomPair F A B pAB →
        IsLeastMixedHomPair F B C pBC →
          pAC.forward = OrderedDomain.compContFun pBC.forward pAB.forward →
            pAC.backward = OrderedDomain.compContFun pAB.backward pBC.backward →
              IsLeastMixedHomPair F A C pAC

/-- Construction evidence for a canonical mixed-variance solution.

The two adjacent stage maps are related by the mixed functor action: an
embedding in the contravariant coordinate is used through its projection, while
an embedding in the covariant coordinate is used directly.  Both expanding
sequences carry the full Chapter 3 laws and both bilimits are identified with
the diagonal solution carrier. -/
structure MixedCanonicalSolutionConstruction
    (F : MixedVariantFunctor.{u}) (S : MixedDomainEquationSolution F) where
  locallyContinuous : def_5_2_5_mixed_variant_locally_continuous F
  baseLeft : OrderedDomain.{u}
  baseRight : OrderedDomain.{u}
  initialLeft :
    Chapter3.EPPair baseLeft.carrier (F.mapObj baseRight baseLeft).carrier
  initialRight :
    Chapter3.EPPair baseRight.carrier (F.mapObj baseLeft baseRight).carrier
  leftSequence :
    Chapter3.ExpandingSequence
      (fun n : Nat => (MixedFunctorLeftObject F baseLeft baseRight n).carrier)
  rightSequence :
    Chapter3.ExpandingSequence
      (fun n : Nat => (MixedFunctorRightObject F baseLeft baseRight n).carrier)
  initial_left_embedding :
    ∀ x : baseLeft.carrier,
      leftSequence.e (Nat.le_succ 0) x = initialLeft.e x
  initial_left_projection :
    ∀ x : (F.mapObj baseRight baseLeft).carrier,
      leftSequence.p (Nat.le_succ 0) x = initialLeft.p x
  initial_right_embedding :
    ∀ x : baseRight.carrier,
      rightSequence.e (Nat.le_succ 0) x = initialRight.e x
  initial_right_projection :
    ∀ x : (F.mapObj baseLeft baseRight).carrier,
      rightSequence.p (Nat.le_succ 0) x = initialRight.p x
  successor_left_embedding :
    ∀ (n : Nat) (x :
        (F.mapObj (MixedFunctorRightObject F baseLeft baseRight n)
          (MixedFunctorLeftObject F baseLeft baseRight n)).carrier),
      leftSequence.e (Nat.le_succ (n + 1)) x =
        F.mapHom
          { toFun := rightSequence.p (Nat.le_succ n)
            continuous := rightSequence.continuous_p (Nat.le_succ n) }
          { toFun := leftSequence.e (Nat.le_succ n)
            continuous := leftSequence.continuous_e (Nat.le_succ n) }
          x
  successor_left_projection :
    ∀ (n : Nat) (x :
        (F.mapObj
          (F.mapObj (MixedFunctorLeftObject F baseLeft baseRight n)
            (MixedFunctorRightObject F baseLeft baseRight n))
          (F.mapObj (MixedFunctorRightObject F baseLeft baseRight n)
            (MixedFunctorLeftObject F baseLeft baseRight n))).carrier),
      leftSequence.p (Nat.le_succ (n + 1)) x =
        F.mapHom
          { toFun := rightSequence.e (Nat.le_succ n)
            continuous := rightSequence.continuous_e (Nat.le_succ n) }
          { toFun := leftSequence.p (Nat.le_succ n)
            continuous := leftSequence.continuous_p (Nat.le_succ n) }
          x
  successor_right_embedding :
    ∀ (n : Nat) (x :
        (F.mapObj (MixedFunctorLeftObject F baseLeft baseRight n)
          (MixedFunctorRightObject F baseLeft baseRight n)).carrier),
      rightSequence.e (Nat.le_succ (n + 1)) x =
        F.mapHom
          { toFun := leftSequence.p (Nat.le_succ n)
            continuous := leftSequence.continuous_p (Nat.le_succ n) }
          { toFun := rightSequence.e (Nat.le_succ n)
            continuous := rightSequence.continuous_e (Nat.le_succ n) }
          x
  successor_right_projection :
    ∀ (n : Nat) (x :
        (F.mapObj
          (F.mapObj (MixedFunctorRightObject F baseLeft baseRight n)
            (MixedFunctorLeftObject F baseLeft baseRight n))
          (F.mapObj (MixedFunctorLeftObject F baseLeft baseRight n)
            (MixedFunctorRightObject F baseLeft baseRight n))).carrier),
      rightSequence.p (Nat.le_succ (n + 1)) x =
        F.mapHom
          { toFun := leftSequence.e (Nat.le_succ n)
            continuous := leftSequence.continuous_e (Nat.le_succ n) }
          { toFun := rightSequence.p (Nat.le_succ n)
            continuous := rightSequence.continuous_p (Nat.le_succ n) }
          x
  left_stage_dcpo :
    ∀ n : Nat,
      Chapter3.IsDcpo (MixedFunctorLeftObject F baseLeft baseRight n).carrier
  left_stage_antisymm :
    ∀ (n : Nat) (x y :
        (MixedFunctorLeftObject F baseLeft baseRight n).carrier),
      x ≤ y → y ≤ x → x = y
  right_stage_dcpo :
    ∀ n : Nat,
      Chapter3.IsDcpo (MixedFunctorRightObject F baseLeft baseRight n).carrier
  right_stage_antisymm :
    ∀ (n : Nat) (x y :
        (MixedFunctorRightObject F baseLeft baseRight n).carrier),
      x ≤ y → y ≤ x → x = y
  solution_left_bilimit_iso :
    Chapter3.OrderIsoData S.object.carrier (Chapter3.Bilimit leftSequence)
  solution_right_bilimit_iso :
    Chapter3.OrderIsoData S.object.carrier (Chapter3.Bilimit rightSequence)
  baseLeft_orderBot : OrderBot baseLeft.carrier
  baseLeft_subsingleton : ∀ x y : baseLeft.carrier, x = y
  baseRight_orderBot : OrderBot baseRight.carrier
  baseRight_subsingleton : ∀ x y : baseRight.carrier, x = y
  solution_orderBot : OrderBot S.object.carrier
  solution_dcpo : Chapter3.IsDcpo S.object.carrier
  solution_antisymm :
    ∀ x y : S.object.carrier, x ≤ y → y ≤ x → x = y
  functor_solution_orderBot : OrderBot (F.mapObj S.object S.object).carrier
  functor_solution_dcpo : Chapter3.IsDcpo (F.mapObj S.object S.object).carrier
  leftStagePair :
    ∀ n : Nat,
      Chapter3.EPPair
        (MixedFunctorLeftObject F baseLeft baseRight n).carrier S.object.carrier
  rightStagePair :
    ∀ n : Nat,
      Chapter3.EPPair
        (MixedFunctorRightObject F baseLeft baseRight n).carrier S.object.carrier
  left_stage_compatible :
    ∀ (n : Nat) (x : (MixedFunctorLeftObject F baseLeft baseRight n).carrier),
      (leftStagePair (n + 1)).e (leftSequence.e (Nat.le_succ n) x) =
        (leftStagePair n).e x
  right_stage_compatible :
    ∀ (n : Nat) (x : (MixedFunctorRightObject F baseLeft baseRight n).carrier),
      (rightStagePair (n + 1)).e (rightSequence.e (Nat.le_succ n) x) =
        (rightStagePair n).e x
  left_stage_zero_strict :
    @Chapter2.StrictMap baseLeft.carrier S.object.carrier inferInstance inferInstance
      baseLeft_orderBot solution_orderBot (leftStagePair 0).e
  right_stage_zero_strict :
    @Chapter2.StrictMap baseRight.carrier S.object.carrier inferInstance inferInstance
      baseRight_orderBot solution_orderBot (rightStagePair 0).e
  left_unfold_stage_embedding :
    ∀ (n : Nat)
      (x : (MixedFunctorLeftObject F baseLeft baseRight (n + 1)).carrier),
      S.unfold ((leftStagePair (n + 1)).e x) =
        F.mapHom (epProjectionContFun (rightStagePair n))
          (epEmbeddingContFun (leftStagePair n)) x
  left_fold_stage_projection :
    ∀ (n : Nat) (x : (F.mapObj S.object S.object).carrier),
      (leftStagePair (n + 1)).p (S.fold x) =
        F.mapHom (epEmbeddingContFun (rightStagePair n))
          (epProjectionContFun (leftStagePair n)) x
  right_unfold_stage_embedding :
    ∀ (n : Nat)
      (x : (MixedFunctorRightObject F baseLeft baseRight (n + 1)).carrier),
      S.unfold ((rightStagePair (n + 1)).e x) =
        F.mapHom (epProjectionContFun (leftStagePair n))
          (epEmbeddingContFun (rightStagePair n)) x
  right_fold_stage_projection :
    ∀ (n : Nat) (x : (F.mapObj S.object S.object).carrier),
      (rightStagePair (n + 1)).p (S.fold x) =
        F.mapHom (epEmbeddingContFun (leftStagePair n))
          (epProjectionContFun (rightStagePair n)) x
  identity_is_sup_left_stage_approximations :
    Chapter3.IsSup
      (Set.range fun n : Nat => epApproximationContFun (leftStagePair n))
      (OrderedDomain.idContFun S.object)
  identity_is_sup_right_stage_approximations :
    Chapter3.IsSup
      (Set.range fun n : Nat => epApproximationContFun (rightStagePair n))
      (OrderedDomain.idContFun S.object)

namespace MixedCanonicalSolutionConstruction

/-- The complete Chapter 3 bilimit package for the left approximation chain. -/
noncomputable def leftBilimitData
    {F : MixedVariantFunctor.{u}} {S : MixedDomainEquationSolution F}
    (C : MixedCanonicalSolutionConstruction F S) :
    Chapter3.ExpandingSequence.BilimitTheoremFullData C.leftSequence
      C.left_stage_dcpo C.left_stage_antisymm :=
  Chapter3.theorem_3_3_7_expanding_sequence_bilimit
    C.leftSequence C.left_stage_dcpo C.left_stage_antisymm

/-- The complete Chapter 3 bilimit package for the right approximation chain. -/
noncomputable def rightBilimitData
    {F : MixedVariantFunctor.{u}} {S : MixedDomainEquationSolution F}
    (C : MixedCanonicalSolutionConstruction F S) :
    Chapter3.ExpandingSequence.BilimitTheoremFullData C.rightSequence
      C.right_stage_dcpo C.right_stage_antisymm :=
  Chapter3.theorem_3_3_7_expanding_sequence_bilimit
    C.rightSequence C.right_stage_dcpo C.right_stage_antisymm

end MixedCanonicalSolutionConstruction

/-- A canonical solution of a mixed-variance equation together with its paired
functor-iteration bilimit construction. -/
structure MixedCanonicalSolution (F : MixedVariantFunctor.{u}) where
  solution : MixedDomainEquationSolution F
  construction : MixedCanonicalSolutionConstruction F solution

/-- A mixed endomorphism of a mixed-variance solution. -/
def IsMixedEndomorphism
    (F : MixedVariantFunctor.{u}) (A : MixedDomainEquationSolution F)
    (h : OrderedDomain.ContFunCarrier A.object A.object) : Prop :=
  ∀ x : (F.mapObj A.object A.object).carrier,
    h (A.fold x) = A.fold (F.mapHom h h x)

/-- Being isomorphic, as a mixed recursive-equation solution, to a canonical
mixed fixed point. -/
def IsCanonicalMixedFixpoint
    (F : MixedVariantFunctor.{u}) (A : MixedDomainEquationSolution F) : Prop :=
  ∃ C : MixedCanonicalSolution F,
    Nonempty (MixedSolutionIso F A C.solution)

/-- The identity is the least mixed endomorphism. -/
def IdentityIsLeastMixedEndomorphism
    (F : MixedVariantFunctor.{u}) (A : MixedDomainEquationSolution F) : Prop :=
  IsMixedEndomorphism F A (OrderedDomain.idContFun A.object) ∧
    ∀ h : OrderedDomain.ContFunCarrier A.object A.object,
      IsMixedEndomorphism F A h → OrderedDomain.idContFun A.object ≤ h

/-- The mixed endomorphism functional `g ↦ fold ∘ F(g,g) ∘ unfold` appearing in
Theorem 5.3.7. -/
def mixedEndomorphismFunctional
    (F : MixedVariantFunctor.{u}) (A : MixedDomainEquationSolution F)
    (g : OrderedDomain.ContFunCarrier A.object A.object) :
    OrderedDomain.ContFunCarrier A.object A.object :=
  OrderedDomain.compContFun A.fold
    (OrderedDomain.compContFun (F.mapHom g g) A.unfold)

/-- The identity is the least fixed point of the mixed endomorphism functional. -/
def IdentityIsLeastMixedFunctionalFixpoint
    (F : MixedVariantFunctor.{u}) (A : MixedDomainEquationSolution F) : Prop :=
  mixedEndomorphismFunctional F A (OrderedDomain.idContFun A.object) =
      OrderedDomain.idContFun A.object ∧
    ∀ h : OrderedDomain.ContFunCarrier A.object A.object,
      mixedEndomorphismFunctional F A h = h →
        OrderedDomain.idContFun A.object ≤ h

/-- The identity is the only mixed endomorphism satisfying an externally supplied
strictness predicate. -/
def IdentityOnlyStrictMixedEndomorphism
    (F : MixedVariantFunctor.{u}) (A : MixedDomainEquationSolution F)
    (Strict : OrderedDomain.ContFunCarrier A.object A.object → Prop) : Prop :=
  ∀ h : OrderedDomain.ContFunCarrier A.object A.object,
    Strict h → IsMixedEndomorphism F A h → h = OrderedDomain.idContFun A.object

/-- The PDF's bottom-preserving strict mixed-endomorphism specialization. -/
def IdentityOnlyBottomStrictMixedEndomorphism
    (F : MixedVariantFunctor.{u}) (A : MixedDomainEquationSolution F)
    [OrderBot A.object.carrier] : Prop :=
  IdentityOnlyStrictMixedEndomorphism F A (fun h => Chapter2.StrictMap h)

/-- Data for the current free mixed-variant algebra interface.  The maps are
bundled continuous maps; PDF strictness hypotheses are tracked separately by
`MixedFreeAlgebraProblem.IsStrict`. -/
structure MixedFreeAlgebraProblem (F : MixedVariantFunctor.{u}) where
  A : OrderedDomain.{u}
  B : OrderedDomain.{u}
  destructA : OrderedDomain.ContFunCarrier A (F.mapObj B A)
  constructB : OrderedDomain.ContFunCarrier (F.mapObj A B) B

/-- Strictness of the two maps in the free mixed-variant algebra problem. -/
def MixedFreeAlgebraProblem.IsStrict
    {F : MixedVariantFunctor.{u}} (P : MixedFreeAlgebraProblem F)
    [OrderBot P.A.carrier] [OrderBot P.B.carrier]
    [OrderBot (F.mapObj P.B P.A).carrier] [OrderBot (F.mapObj P.A P.B).carrier] :
    Prop :=
  P.destructA ⊥ = ⊥ ∧ P.constructB ⊥ = ⊥

/-- A solution pair for the current free mixed-variant algebra problem.  The
solution maps are continuous maps; PDF strictness is tracked separately by
`MixedFreeAlgebraSolution.IsStrict`. -/
structure MixedFreeAlgebraSolution
    (F : MixedVariantFunctor.{u}) (D : MixedDomainEquationSolution F)
    (P : MixedFreeAlgebraProblem F) where
  toCanonical : OrderedDomain.ContFunCarrier P.A D.object
  fromCanonical : OrderedDomain.ContFunCarrier D.object P.B
  left_square :
    ∀ x : P.A.carrier,
      D.unfold (toCanonical x) =
        F.mapHom fromCanonical toCanonical (P.destructA x)
  right_square :
    ∀ x : (F.mapObj D.object D.object).carrier,
      fromCanonical (D.fold x) =
        P.constructB (F.mapHom toCanonical fromCanonical x)

/-- Strictness of the unique maps supplied by the free mixed-variant algebra theorem. -/
def MixedFreeAlgebraSolution.IsStrict
    {F : MixedVariantFunctor.{u}} {D : MixedDomainEquationSolution F}
    {P : MixedFreeAlgebraProblem F} (S : MixedFreeAlgebraSolution F D P)
    [OrderBot P.A.carrier] [OrderBot P.B.carrier] [OrderBot D.object.carrier] :
    Prop :=
  S.toCanonical ⊥ = ⊥ ∧ S.fromCanonical ⊥ = ⊥

/-- Uniqueness for the free mixed-variant algebra solution pair. -/
def IsUniqueMixedFreeAlgebraSolution
    (F : MixedVariantFunctor.{u}) (D : MixedDomainEquationSolution F)
    (P : MixedFreeAlgebraProblem F) (S : MixedFreeAlgebraSolution F D P)
    [OrderBot P.A.carrier] [OrderBot P.B.carrier] [OrderBot D.object.carrier] : Prop :=
  ∀ T : MixedFreeAlgebraSolution F D P,
    MixedFreeAlgebraSolution.IsStrict T →
      T.toCanonical = S.toCanonical ∧ T.fromCanonical = S.fromCanonical

/-- Compatibility name for Definition 5.2.5.  It contains exactly the
mixed-variant local-continuity data from the source; the later least-hom,
invariance, and free-algebra results are separate theorems in Section 5.3. -/
abbrev def_5_2_5_mixed_variant_functor (F : MixedVariantFunctor.{u}) : Prop :=
  def_5_2_5_mixed_variant_locally_continuous F

/-- The covariant action on embeddings induced by a mixed-variance functor. -/
def MixedVariantFunctor.mapEmbedding
    (F : MixedVariantFunctor.{u}) {D₁ D₂ E₁ E₂ : OrderedDomain.{u}}
    (e : DomainEmbedding D₁ D₂) (e' : DomainEmbedding E₁ E₂) :
    OrderedDomain.ContFunCarrier (F.mapObj D₁ E₁) (F.mapObj D₂ E₂) :=
  F.mapHom (DomainEmbedding.projection e) (DomainEmbedding.embedding e')

/-- Proposition 5.2.6.  The mixed-variant action sends a pair of embeddings to
an embedding with embedding component `F(e^*,e')`, upper adjoint
`F(e,e'^*)`, and a Scott-continuous action on the ambient hom-posets. -/
theorem prop_5_2_6_mixed_variant_chains
    (F : MixedVariantFunctor.{u}) (hF : def_5_2_5_mixed_variant_functor F)
    {D₁ D₂ E₁ E₂ : OrderedDomain.{u}}
    (e : DomainEmbedding D₁ D₂) (e' : DomainEmbedding E₁ E₂) :
    ∃ mapped : DomainEmbedding (F.mapObj D₁ E₁) (F.mapObj D₂ E₂),
      (∀ x : (F.mapObj D₁ E₁).carrier,
        mapped.embedding x = F.mapEmbedding e e' x) ∧
      (∀ y : (F.mapObj D₂ E₂).carrier,
        mapped.projection y =
          F.mapHom (DomainEmbedding.embedding e) (DomainEmbedding.projection e') y) ∧
      Chapter3.ScottContinuous
        (fun p : OrderedDomain.ContFunCarrier D₂ D₁ ×
            OrderedDomain.ContFunCarrier E₁ E₂ => F.mapHom p.1 p.2) := by
  let mapped : DomainEmbedding (F.mapObj D₁ E₁) (F.mapObj D₂ E₂) :=
    { pair :=
        { e := F.mapEmbedding e e'
          p := F.mapHom (DomainEmbedding.embedding e) (DomainEmbedding.projection e')
          continuous_e := (F.mapEmbedding e e').continuous
          continuous_p :=
            (F.mapHom (DomainEmbedding.embedding e)
              (DomainEmbedding.projection e')).continuous
          retract := by
            intro x
            calc
              F.mapHom (DomainEmbedding.embedding e) (DomainEmbedding.projection e')
                  (F.mapEmbedding e e' x)
                  = F.mapHom
                      (OrderedDomain.compContFun (DomainEmbedding.projection e)
                        (DomainEmbedding.embedding e))
                      (OrderedDomain.compContFun (DomainEmbedding.projection e')
                        (DomainEmbedding.embedding e')) x := by
                    exact F.mapHom_comp (DomainEmbedding.projection e)
                      (DomainEmbedding.embedding e) (DomainEmbedding.embedding e')
                      (DomainEmbedding.projection e') x
              _ = F.mapHom (OrderedDomain.idContFun D₁)
                  (OrderedDomain.idContFun E₁) x := by
                    exact F.mapHom_congr
                      (fun y => e.pair.retract y) (fun y => e'.pair.retract y) x
              _ = x := F.mapHom_id x
          below := by
            intro y
            have hmono :=
              Chapter3.ScottContinuous.monotone
                (hF.hom_continuous
                  (D₁ := D₂) (D₂ := D₂) (E₁ := E₂) (E₂ := E₂))
            have hpair :
                (OrderedDomain.compContFun (DomainEmbedding.embedding e)
                    (DomainEmbedding.projection e),
                  OrderedDomain.compContFun (DomainEmbedding.embedding e')
                    (DomainEmbedding.projection e')) ≤
                (OrderedDomain.idContFun D₂, OrderedDomain.idContFun E₂) := by
              constructor
              · intro z
                exact e.pair.below z
              · intro z
                exact e'.pair.below z
            calc
              F.mapEmbedding e e'
                  (F.mapHom (DomainEmbedding.embedding e)
                    (DomainEmbedding.projection e') y)
                  = F.mapHom
                      (OrderedDomain.compContFun (DomainEmbedding.embedding e)
                        (DomainEmbedding.projection e))
                      (OrderedDomain.compContFun (DomainEmbedding.embedding e')
                        (DomainEmbedding.projection e')) y := by
                    exact F.mapHom_comp (DomainEmbedding.embedding e)
                      (DomainEmbedding.projection e) (DomainEmbedding.projection e')
                      (DomainEmbedding.embedding e') y
              _ ≤ F.mapHom (OrderedDomain.idContFun D₂)
                  (OrderedDomain.idContFun E₂) y := hmono hpair y
              _ = y := F.mapHom_id y } }
  refine ⟨mapped, ?_, ?_,
    hF.hom_continuous
      (D₁ := D₁) (D₂ := D₂) (E₁ := E₁) (E₂ := E₂)⟩
  · intro x
    rfl
  · intro y
    rfl

/-- Domain-completeness data for the chosen fixed point of every frozen
endofunctor `F(D,-)`.  These are ambient category assumptions, not conclusions
about the parameterized morphism action. -/
structure ParameterizedCanonicalSolutions (F : BinaryDomainFunctor.{u}) where
  solution : ∀ D : OrderedDomain.{u}, DomainEquationSolution (F.fixedEndofunctor D)
  object_orderBot : ∀ D : OrderedDomain.{u}, OrderBot (solution D).object.carrier
  object_dcpo : ∀ D : OrderedDomain.{u}, Chapter3.IsDcpo (solution D).object.carrier
  object_antisymm :
    ∀ (D : OrderedDomain.{u}) (x y : (solution D).object.carrier),
      x ≤ y → y ≤ x → x = y
  functor_object_dcpo :
    ∀ D : OrderedDomain.{u},
      Chapter3.IsDcpo (F.mapObj D (solution D).object).carrier

/-- The pointwise partial order on a continuous-function space when the
codomain preorder is explicitly antisymmetric. -/
@[reducible] def contFunPartialOrderOfAntisymm
    (D E : OrderedDomain.{u})
    (hEanti : ∀ x y : E.carrier, x ≤ y → y ≤ x → x = y) :
    PartialOrder (OrderedDomain.ContFunCarrier D E) where
  le f g := ∀ x, f x ≤ g x
  le_refl f x := le_rfl
  le_trans f g h hfg hgh x := le_trans (hfg x) (hgh x)
  le_antisymm f g hfg hgf := by
    apply Chapter3.ContFun.ext_apply
    intro x
    exact hEanti _ _ (hfg x) (hgf x)

/-- The joint recursive functional used to define the action of the
parameterized fixed-point functor on a morphism `f : D -> E`. -/
def parameterizedHomFunctional
    (F : BinaryDomainFunctor.{u}) (S : ParameterizedCanonicalSolutions F)
    (D E : OrderedDomain.{u})
    (p : OrderedDomain.ContFunCarrier D E ×
      OrderedDomain.ContFunCarrier (S.solution D).object (S.solution E).object) :
    OrderedDomain.ContFunCarrier (S.solution D).object (S.solution E).object :=
  OrderedDomain.compContFun (S.solution E).fold
    (OrderedDomain.compContFun (F.mapHom p.1 p.2) (S.solution D).unfold)

/-- The joint parameter-and-recursive-map functional is Scott-continuous. -/
theorem parameterizedHomFunctional_scottContinuous
    (F : BinaryDomainFunctor.{u}) (hF : LocallyContinuousBinary F)
    (S : ParameterizedCanonicalSolutions F) (D E : OrderedDomain.{u}) :
    Chapter3.ScottContinuous (parameterizedHomFunctional F S D E) := by
  let hMap := hF.hom_continuous
    (D₁ := D) (D₂ := E)
    (E₁ := (S.solution D).object) (E₂ := (S.solution E).object)
  have hWhisker : Chapter3.ScottContinuous
      (fun q : OrderedDomain.ContFunCarrier
          (F.mapObj D (S.solution D).object)
          (F.mapObj E (S.solution E).object) =>
        OrderedDomain.compContFun (S.solution E).fold
          (OrderedDomain.compContFun q (S.solution D).unfold)) := by
    constructor
    · intro f g hfg x
      exact (S.solution E).fold.continuous.1 (hfg ((S.solution D).unfold x))
    · intro G s hG hs
      constructor
      · intro y hy
        rcases hy with ⟨g, hg, rfl⟩
        intro x
        exact (S.solution E).fold.continuous.1
          (hs.1 hg ((S.solution D).unfold x))
      · intro q hq x
        have hEvalSup :=
          (Chapter3.ContFun.eval_scottContinuous
            (S.functor_object_dcpo E) ((S.solution D).unfold x)).2 hG hs
        have hEvalDir : Chapter3.DirectedSet
            ((fun g : OrderedDomain.ContFunCarrier
                (F.mapObj D (S.solution D).object)
                (F.mapObj E (S.solution E).object) =>
              g ((S.solution D).unfold x)) '' G) :=
          Chapter3.DirectedSet.image
            (Chapter3.ContFun.eval_scottContinuous
              (S.functor_object_dcpo E) ((S.solution D).unfold x)).1 hG
        have hFoldSup := (S.solution E).fold.continuous.2 hEvalDir hEvalSup
        apply hFoldSup.2 (q x)
        intro y hy
        rcases hy with ⟨z, hz, rfl⟩
        rcases hz with ⟨g, hg, rfl⟩
        exact hq ⟨g, hg, rfl⟩ x
  change Chapter3.ScottContinuous
    (fun p : OrderedDomain.ContFunCarrier D E ×
        OrderedDomain.ContFunCarrier (S.solution D).object (S.solution E).object =>
      OrderedDomain.compContFun (S.solution E).fold
      (OrderedDomain.compContFun (F.mapHom p.1 p.2) (S.solution D).unfold))
  exact Chapter3.ScottContinuous.comp
    (f := fun q : OrderedDomain.ContFunCarrier
        (F.mapObj D (S.solution D).object) (F.mapObj E (S.solution E).object) =>
      OrderedDomain.compContFun (S.solution E).fold
        (OrderedDomain.compContFun q (S.solution D).unfold))
    (g := fun p : OrderedDomain.ContFunCarrier D E ×
        OrderedDomain.ContFunCarrier (S.solution D).object (S.solution E).object =>
      F.mapHom p.1 p.2)
    hWhisker hMap

/-- Bundle the joint functional and curry its parameter coordinate. -/
def parameterizedFunctionalAssignment
    (F : BinaryDomainFunctor.{u}) (hF : LocallyContinuousBinary F)
    (S : ParameterizedCanonicalSolutions F) (D E : OrderedDomain.{u}) :
    Chapter3.ContFun
      (OrderedDomain.ContFunCarrier D E)
      (Chapter2.ScottContFun
        (OrderedDomain.ContFunCarrier (S.solution D).object (S.solution E).object)
        (OrderedDomain.ContFunCarrier (S.solution D).object (S.solution E).object)) := by
  let joint : Chapter3.ContFun
      (OrderedDomain.ContFunCarrier D E ×
        OrderedDomain.ContFunCarrier (S.solution D).object (S.solution E).object)
      (OrderedDomain.ContFunCarrier (S.solution D).object (S.solution E).object) :=
    { toFun := parameterizedHomFunctional F S D E
      continuous := parameterizedHomFunctional_scottContinuous F hF S D E }
  have hSeparate :=
    (Chapter3.lemma_3_2_6_continuous_iff_separately_continuous
      (fun p => joint p)).1 joint.continuous
  exact
    { toFun := fun f =>
        { toFun := fun g => joint (f, g)
          continuous := hSeparate.1 f }
      continuous := by
        constructor
        · intro f g hfg x
          exact joint.continuous.1 ⟨hfg, le_rfl⟩
        · intro A s hA hs
          constructor
          · intro y hy x
            rcases hy with ⟨f, hf, rfl⟩
            exact joint.continuous.1 ⟨hs.1 hf, le_rfl⟩
          · intro q hq x
            have hxSup := (hSeparate.2 x).2 hA hs
            apply hxSup.2 (q x)
            intro y hy
            rcases hy with ⟨f, hf, rfl⟩
            exact hq ⟨f, hf, rfl⟩ x }

/-- The morphism action obtained by taking the least fixed point of the
parameterized homomorphism functional. -/
noncomputable def parameterizedFixMap
    (F : BinaryDomainFunctor.{u}) (hF : LocallyContinuousBinary F)
    (S : ParameterizedCanonicalSolutions F)
    {D E : OrderedDomain.{u}} (f : OrderedDomain.ContFunCarrier D E) :
    OrderedDomain.ContFunCarrier (S.solution D).object (S.solution E).object := by
  letI targetBot : OrderBot (S.solution E).object.carrier := S.object_orderBot E
  let H := OrderedDomain.ContFunCarrier (S.solution D).object (S.solution E).object
  letI : PartialOrder H := contFunPartialOrderOfAntisymm
    (S.solution D).object (S.solution E).object (S.object_antisymm E)
  letI : OrderBot H :=
    { bot := Chapter3.ContFun.const (⊥ : (S.solution E).object.carrier)
      bot_le := fun _ _ => bot_le }
  exact Chapter2.chosenLeastFix
    (Chapter3.ContFun.isDcpo_of_codomain (S.object_dcpo E))
    (parameterizedFunctionalAssignment F hF S D E f)

/-- The parameterized least-fixed-point morphism action is locally
Scott-continuous. -/
theorem parameterizedFixMap_scottContinuous
    (F : BinaryDomainFunctor.{u}) (hF : LocallyContinuousBinary F)
    (S : ParameterizedCanonicalSolutions F) {D E : OrderedDomain.{u}} :
    Chapter3.ScottContinuous
      (fun f : OrderedDomain.ContFunCarrier D E =>
        parameterizedFixMap F hF S f) := by
  letI targetBot : OrderBot (S.solution E).object.carrier := S.object_orderBot E
  let H := OrderedDomain.ContFunCarrier (S.solution D).object (S.solution E).object
  letI : PartialOrder H := contFunPartialOrderOfAntisymm
    (S.solution D).object (S.solution E).object (S.object_antisymm E)
  letI : OrderBot H :=
    { bot := Chapter3.ContFun.const (⊥ : (S.solution E).object.carrier)
      bot_le := fun _ _ => bot_le }
  change Chapter3.ScottContinuous
    (fun f : OrderedDomain.ContFunCarrier D E =>
      Chapter2.chosenLeastFix
        (Chapter3.ContFun.isDcpo_of_codomain (S.object_dcpo E))
        (parameterizedFunctionalAssignment F hF S D E f))
  exact Chapter3.ScottContinuous.comp
    (Chapter2.theorem_2_1_19_2_fix_assignment_continuous
      (Chapter3.ContFun.isDcpo_of_codomain (S.object_dcpo E)))
    (parameterizedFunctionalAssignment F hF S D E).continuous

/-- Proposition 5.2.7.  PDF text: for a locally continuous binary functor
`F : D_⊥! × E_⊥! -> E_⊥!`, the assignment
`D |-> FIX(F(D,-))` and the displayed supremum formula on morphisms define a
locally continuous functor.

The chosen fixed-point data make the ambient domain-category assumptions
explicit; the morphism action and its local continuity are derived above from
the printed recursive functional and the continuous least-fixed-point operator. -/
theorem prop_5_2_7_parameterized_fix_locally_continuous
    (F : BinaryDomainFunctor.{u}) (hF : LocallyContinuousBinary F)
    (S : ParameterizedCanonicalSolutions F) :
    ∃ FIX : ParameterizedFixFunctor F, FIX.locallyContinuous := by
  let FIX : ParameterizedFixFunctor F :=
    { mapObj := fun D => (S.solution D).object
      solution := S.solution
      mapObj_eq_solution := fun _ => rfl
      mapHom := fun {_D _E} f => parameterizedFixMap F hF S f
      locallyContinuous := True
      locallyContinuous_iff := by
        constructor
        · intro _ D E
          exact parameterizedFixMap_scottContinuous F hF S (D := D) (E := E)
        · intro _
          trivial }
  exact ⟨FIX, trivial⟩

end Chapter5
end AbramskyJung

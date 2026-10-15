import Practice.DomainTheory.Chapter03.NumberedItems.Section33_BilimitPreservation

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Chapter 3: Section 3.3 function-space closure

Book-facing declarations and their local support API are kept together in
textbook dependency order. Reusable constructions remain in the concept-owned
`Chapter03.Section*` modules.
-/

universe u v w z l

namespace AbramskyJung
namespace Chapter3

namespace StrictContFun

/-- Evaluation of a directed family of strict maps is directed pointwise. -/
theorem eval_directed
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    {A : Set (StrictContFun D E)} (hA : DirectedSet A) (d : D) :
    DirectedSet ((fun f : StrictContFun D E => f d) '' A) :=
  DirectedSet.image (f := fun f : StrictContFun D E => f d)
    (by intro f g hfg; exact hfg d) hA

/-- Pointwise supremum of a directed family of strict continuous maps. -/
noncomputable def directedSupFun
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (StrictContFun D E)) (hA : DirectedSet A) :
    D → E :=
  fun d => Classical.choose (hE ((fun f : StrictContFun D E => f d) '' A)
    (StrictContFun.eval_directed hA d))

/-- The pointwise value of `directedSupFun` is the supremum of the pointwise
evaluation set. -/
theorem directedSupFun_isSup_eval
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (StrictContFun D E)) (hA : DirectedSet A)
    (d : D) :
    IsSup ((fun f : StrictContFun D E => f d) '' A)
      (StrictContFun.directedSupFun hE A hA d) :=
  Classical.choose_spec (hE ((fun f : StrictContFun D E => f d) '' A)
    (StrictContFun.eval_directed hA d))

/-- The pointwise directed supremum of strict continuous maps is monotone. -/
theorem directedSupFun_monotone
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (StrictContFun D E)) (hA : DirectedSet A) :
    Monotone (StrictContFun.directedSupFun hE A hA) := by
  intro d e hde
  exact (StrictContFun.directedSupFun_isSup_eval hE A hA d).2
    (StrictContFun.directedSupFun hE A hA e) (by
      intro y hy
      rcases hy with ⟨f, hfA, rfl⟩
      exact le_trans (f.continuous.1 hde)
        ((StrictContFun.directedSupFun_isSup_eval hE A hA e).1 ⟨f, hfA, rfl⟩))

/-- The pointwise directed supremum of strict continuous maps is
Scott-continuous. -/
theorem directedSupFun_scottContinuous
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (StrictContFun D E)) (hA : DirectedSet A) :
    ScottContinuous (StrictContFun.directedSupFun hE A hA) := by
  constructor
  · exact StrictContFun.directedSupFun_monotone hE A hA
  · intro B s hB hs
    constructor
    · intro y hy
      rcases hy with ⟨b, hb, rfl⟩
      exact StrictContFun.directedSupFun_monotone hE A hA (hs.1 hb)
    · intro y hy
      exact (StrictContFun.directedSupFun_isSup_eval hE A hA s).2 y (by
        intro z hz
        rcases hz with ⟨f, hfA, rfl⟩
        exact (f.continuous.2 hB hs).2 y (by
          intro fb hfb
          rcases hfb with ⟨b, hb, rfl⟩
          exact le_trans
            ((StrictContFun.directedSupFun_isSup_eval hE A hA b).1 ⟨f, hfA, rfl⟩)
            (hy ⟨b, hb, rfl⟩)))

/-- The pointwise directed supremum of strict maps is still strict. -/
theorem directedSupFun_preservesLeast
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (StrictContFun D E)) (hA : DirectedSet A) :
    PreservesLeastElement (StrictContFun.directedSupFun hE A hA) := by
  intro d hd y
  exact (StrictContFun.directedSupFun_isSup_eval hE A hA d).2 y (by
    intro z hz
    rcases hz with ⟨f, _hfA, rfl⟩
    exact f.strict d hd y)

/-- Directed supremum in the strict continuous function space. -/
noncomputable def directedSup
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (StrictContFun D E)) (hA : DirectedSet A) :
    StrictContFun D E where
  toFun := StrictContFun.directedSupFun hE A hA
  continuous := StrictContFun.directedSupFun_scottContinuous hE A hA
  strict := StrictContFun.directedSupFun_preservesLeast hE A hA

/-- The constructed pointwise strict function is the supremum of the directed
family. -/
theorem directedSup_isSup
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (StrictContFun D E)) (hA : DirectedSet A) :
    IsSup A (StrictContFun.directedSup hE A hA) := by
  constructor
  · intro f hfA x
    change f x ≤ StrictContFun.directedSupFun hE A hA x
    exact (StrictContFun.directedSupFun_isSup_eval hE A hA x).1 ⟨f, hfA, rfl⟩
  · intro g hg x
    change StrictContFun.directedSupFun hE A hA x ≤ g x
    exact (StrictContFun.directedSupFun_isSup_eval hE A hA x).2 (g x) (by
      intro y hy
      rcases hy with ⟨f, hfA, rfl⟩
      exact hg hfA x)

/-- If the codomain is a dcpo, then strict continuous maps into it form a dcpo
under the pointwise order. -/
theorem isDcpo_of_codomain
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) : IsDcpo (StrictContFun D E) := by
  intro A hA
  exact ⟨StrictContFun.directedSup hE A hA, StrictContFun.directedSup_isSup hE A hA⟩

/-- Evaluation at a point is Scott-continuous for strict continuous maps under
the pointwise function-space dcpo. -/
theorem eval_scottContinuous
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (d : D) : ScottContinuous (fun f : StrictContFun D E => f d) := by
  constructor
  · intro f g hfg
    exact hfg d
  · intro A s hA hs
    constructor
    · intro y hy
      rcases hy with ⟨f, hfA, rfl⟩
      exact hs.1 hfA d
    · intro y hy
      have hPointSup : IsSup A (StrictContFun.directedSup hE A hA) :=
        StrictContFun.directedSup_isSup hE A hA
      exact le_trans ((hs.2 (StrictContFun.directedSup hE A hA) hPointSup.1) d)
        ((StrictContFun.directedSupFun_isSup_eval hE A hA d).2 y hy)

/-- The application map `[D -> E]! × D -> E` is Scott-continuous. -/
theorem apply_scottContinuous
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) :
    ScottContinuous (fun p : StrictContFun D E × D => p.1 p.2) := by
  exact (lemma_3_2_6_continuous_iff_separately_continuous
    (fun p : StrictContFun D E × D => p.1 p.2)).2
    ⟨fun f => f.continuous, fun d => StrictContFun.eval_scottContinuous hE d⟩

/-- Support for Theorem 3.3.4: a least codomain element gives the constant
least strict continuous function. -/
def const {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (e : E) (he : Chapter2.IsLeast e) : StrictContFun D E where
  toFun := fun _ => e
  continuous := const_scottContinuous e
  strict := fun _ _ => he

/-- The constant least strict function is least in the pointwise order. -/
theorem const_isLeast
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] {e : E}
    (he : Chapter2.IsLeast e) :
    Chapter2.IsLeast (StrictContFun.const (D := D) (E := E) e he) := by
  intro f x
  exact he (f x)

/-- A pointed codomain makes the strict continuous function space pointed. -/
theorem hasLeastElement_of_codomain
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : HasLeastElement E) : HasLeastElement (StrictContFun D E) := by
  rcases hE with ⟨e, he⟩
  exact ⟨StrictContFun.const (D := D) (E := E) e he, StrictContFun.const_isLeast he⟩

/-- Antisymmetry of the codomain transfers to strict continuous functions. -/
theorem antisymmetric_of_codomain
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsAntisymmetricOrder E) : IsAntisymmetricOrder (StrictContFun D E) := by
  intro f g hfg hgf
  cases f with
  | mk f hf hs =>
      cases g with
      | mk g hg gs =>
          have hfun : f = g := funext fun x => hE (f x) (g x) (hfg x) (hgf x)
          subst hfun
          congr

end StrictContFun

namespace StrictContFun

/-- The strict continuous function-space carrier is a pointed partial-order
dcpo whenever the codomain is. -/
theorem strictPointedFunctionSpaceObjectSupport :
    StrictPointedFunctionSpaceObjectSupport.{u} := by
  intro D E _ _ _hDdcpo _hDanti _hDpointed hEdcpo hEanti hEpointed
  exact ⟨StrictContFun.isDcpo_of_codomain hEdcpo,
    StrictContFun.antisymmetric_of_codomain hEanti,
    StrictContFun.hasLeastElement_of_codomain hEpointed⟩

/-- The concrete strict continuous function space supplies the strict-pointed
internal-hom comparison. -/
theorem strictPointedInternalHomComparison :
    StrictPointedInternalHomComparison.{u} := by
  intro D E _ _ _hDdcpo _hDanti _hDpointed hEdcpo hEanti hEpointed
  refine ⟨StrictContFun D E, inferInstance, ?_, ?_, ?_, ?_⟩
  · exact StrictContFun.isDcpo_of_codomain hEdcpo
  · exact StrictContFun.antisymmetric_of_codomain hEanti
  · exact StrictContFun.hasLeastElement_of_codomain hEpointed
  · exact ⟨OrderIsoData.refl (StrictContFun D E)⟩

/-- Build the current strict-pointed monoidal-closed interface once the strict
internal-hom comparison is supplied.  The smash tensor-hom adjunction is
registered separately by `StrictPointedTensorHomAdjunction`. -/
theorem strictPointedDCPOMonoidalClosedCore_of_internalHomComparison
    (h : StrictPointedInternalHomComparison.{u}) :
    StrictPointedDCPOMonoidalClosedCore.{u} :=
  ⟨StrictContFun.strictPointedFunctionSpaceObjectSupport, h⟩

/-- The object/internal-hom component supplied by the concrete strict function
space.  The tensor-hom component is constructed below. -/
theorem strictPointedDCPOMonoidalClosedCore :
    StrictPointedDCPOMonoidalClosedCore.{u} :=
  StrictContFun.strictPointedDCPOMonoidalClosedCore_of_internalHomComparison
    StrictContFun.strictPointedInternalHomComparison

/-- One direction of the smash tensor/function-space adjunction: a strict
continuous map out of the smash product curries to a strict continuous map into
the strict function space.  This is support for Theorem 3.3.4's tensor-hom
adjunction; the inverse uncurrying direction and order-isomorphism package are
not claimed here. -/
noncomputable def smashCurryBundled
    {D : Type u} {E : Type v} {F : Type w}
    [Preorder D] [Preorder E] [Preorder F] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    (f : StrictContFun (SmashProduct D E) F) :
    StrictContFun D (StrictContFun E F) where
  toFun := fun d =>
    { toFun := fun e => f (SmashProduct.mk (D := D) (E := E) d e)
      continuous :=
        ScottContinuous.comp f.continuous
          (SmashProduct.mk_right_section_scottContinuous (D := D) (E := E)
            hDbot hEbot d)
      strict := by
        intro e he
        have hebot : e = ⊥ := hEbot e (he ⊥)
        subst e
        change Chapter2.IsLeast (f (SmashProduct.mk (D := D) (E := E) d ⊥))
        rw [SmashProduct.mk_bot_right (D := D) (E := E) d]
        exact f.strict (⊥ : SmashProduct D E)
          (SmashProduct.bot_isLeast (D := D) (E := E)) }
  continuous := by
    constructor
    · intro d₁ d₂ hd e
      exact f.continuous.1
        (SmashProduct.mk_monotone (D := D) (E := E) hDbot hEbot
          (show (d₁, e) ≤ (d₂, e) from ⟨hd, le_rfl⟩))
    · intro A s hA hs
      constructor
      · intro y hy e
        rcases hy with ⟨d, hdA, rfl⟩
        exact f.continuous.1
          (SmashProduct.mk_monotone (D := D) (E := E) hDbot hEbot
            (show (d, e) ≤ (s, e) from ⟨hs.1 hdA, le_rfl⟩))
      · intro g hg e
        have hsection :
            ScottContinuous (fun d : D => SmashProduct.mk (D := D) (E := E) d e) :=
          SmashProduct.mk_left_section_scottContinuous (D := D) (E := E)
            hDbot hEbot e
        have hsectionSup :
            IsSup ((fun d : D => SmashProduct.mk (D := D) (E := E) d e) '' A)
              (SmashProduct.mk (D := D) (E := E) s e) :=
          hsection.2 hA hs
        have hsectionDir :
            DirectedSet ((fun d : D => SmashProduct.mk (D := D) (E := E) d e) '' A) :=
          DirectedSet.image hsection.1 hA
        have hfSup :
            IsSup
              (f '' ((fun d : D => SmashProduct.mk (D := D) (E := E) d e) '' A))
              (f (SmashProduct.mk (D := D) (E := E) s e)) :=
          f.continuous.2 hsectionDir hsectionSup
        exact hfSup.2 (g e) (by
          intro y hy
          rcases hy with ⟨z, hz, rfl⟩
          rcases hz with ⟨d, hdA, rfl⟩
          exact hg ⟨d, hdA, rfl⟩ e)
  strict := by
    intro d hd g e
    have hdbot : d = ⊥ := hDbot d (hd ⊥)
    subst d
    change f (SmashProduct.mk (D := D) (E := E) ⊥ e) ≤ g e
    rw [SmashProduct.mk_bot_left (D := D) (E := E)]
    exact f.strict (⊥ : SmashProduct D E)
      (SmashProduct.bot_isLeast (D := D) (E := E)) (g e)

/-- The other direction of the concrete smash tensor/function-space adjunction:
a strict continuous map into the strict function space uncurries to a strict
continuous map out of the smash product.  This still does not claim the full
order-isomorphism package. -/
noncomputable def smashUncurryBundled
    {D : Type u} {E : Type v} {F : Type w}
    [Preorder D] [Preorder E] [Preorder F] [OrderBot D] [OrderBot E]
    (hF : IsDcpo F)
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    (g : StrictContFun D (StrictContFun E F)) :
    StrictContFun (SmashProduct D E) F where
  toFun := fun z => g (SmashProduct.toProd (D := D) (E := E) z).1
    (SmashProduct.toProd (D := D) (E := E) z).2
  continuous := by
    have hProduct :
        ScottContinuous (fun p : D × E => g p.1 p.2) := by
      exact (lemma_3_2_6_continuous_iff_separately_continuous
        (fun p : D × E => g p.1 p.2)).2
        ⟨fun d => (g d).continuous,
          fun e => ScottContinuous.comp
            (StrictContFun.eval_scottContinuous hF e) g.continuous⟩
    exact ScottContinuous.comp
      (f := fun p : D × E => g p.1 p.2)
      (g := SmashProduct.toProd (D := D) (E := E))
      hProduct
      (SmashProduct.toProd_scottContinuous (D := D) (E := E) hDbot hEbot)
  strict := by
    intro z hz y
    have hzbot : z = (⊥ : SmashProduct D E) :=
      SmashProduct.eq_bot_of_le_bot (D := D) (E := E) (hz ⊥)
    subst z
    change g ⊥ ⊥ ≤ y
    exact (g ⊥).strict ⊥ (fun e : E => bot_le) y

/-- Uncurrying after currying a strict map out of the smash product returns the
original strict map. -/
theorem smashUncurry_smashCurryBundled
    {D : Type u} {E : Type v} {F : Type w}
    [Preorder D] [Preorder E] [Preorder F] [OrderBot D] [OrderBot E]
    (hF : IsDcpo F)
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    (f : StrictContFun (SmashProduct D E) F) :
    StrictContFun.smashUncurryBundled hF hDbot hEbot
        (StrictContFun.smashCurryBundled hDbot hEbot f) = f := by
  apply StrictContFun.ext_apply
  intro z
  change f (SmashProduct.mk (D := D) (E := E)
    (SmashProduct.toProd (D := D) (E := E) z).1
    (SmashProduct.toProd (D := D) (E := E) z).2) = f z
  rw [SmashProduct.mk_toProd (D := D) (E := E) z]

/-- Currying after uncurrying a strict map into the strict function space
returns the original map.  The codomain antisymmetry hypothesis is needed in
the local preorder interface to identify the two least values produced when a
smash coordinate is bottom. -/
theorem smashCurry_smashUncurryBundled
    {D : Type u} {E : Type v} {F : Type w}
    [Preorder D] [Preorder E] [Preorder F] [OrderBot D] [OrderBot E]
    (hFdcpo : IsDcpo F) (hFanti : IsAntisymmetricOrder F)
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    (g : StrictContFun D (StrictContFun E F)) :
    StrictContFun.smashCurryBundled hDbot hEbot
        (StrictContFun.smashUncurryBundled hFdcpo hDbot hEbot g) = g := by
  apply StrictContFun.ext_apply
  intro d
  apply StrictContFun.ext_apply
  intro e
  change
    g (SmashProduct.toProd (D := D) (E := E)
        (SmashProduct.mk (D := D) (E := E) d e)).1
      (SmashProduct.toProd (D := D) (E := E)
        (SmashProduct.mk (D := D) (E := E) d e)).2 = g d e
  by_cases hd : d = ⊥
  · subst d
    rw [SmashProduct.mk_bot_left (D := D) (E := E)]
    have hleastFun : Chapter2.IsLeast (g (⊥ : D)) :=
      g.strict ⊥ (fun x : D => bot_le)
    have hleastValue : Chapter2.IsLeast ((g (⊥ : D)) ⊥) :=
      (g (⊥ : D)).strict ⊥ (fun y : E => bot_le)
    have hle₁ : (g (⊥ : D)) ⊥ ≤ (g (⊥ : D)) e := hleastValue _
    let hconst :
        StrictContFun E F :=
      StrictContFun.const (D := E) (E := F) ((g (⊥ : D)) ⊥) hleastValue
    have hle₂ : (g (⊥ : D)) e ≤ (g (⊥ : D)) ⊥ := by
      have hle₂' := hleastFun hconst e
      change (g (⊥ : D)) e ≤ hconst e at hle₂'
      simpa [hconst, StrictContFun.const] using hle₂'
    exact hFanti _ _ hle₁ hle₂
  · by_cases he : e = ⊥
    · subst e
      rw [SmashProduct.mk_bot_right (D := D) (E := E)]
      have hleastFun : Chapter2.IsLeast (g (⊥ : D)) :=
        g.strict ⊥ (fun x : D => bot_le)
      have hle₁ : (g (⊥ : D)) ⊥ ≤ (g d) ⊥ := hleastFun (g d) ⊥
      have hleastValue : Chapter2.IsLeast ((g d) ⊥) :=
        (g d).strict ⊥ (fun y : E => bot_le)
      have hle₂ : (g d) ⊥ ≤ (g (⊥ : D)) ⊥ := hleastValue _
      exact hFanti _ _ hle₁ hle₂
    · rw [SmashProduct.mk_of_ne (D := D) (E := E) hd he]
      simp [SmashProduct.toProd]

/-- Concrete order-isomorphism data for the smash tensor/function-space
correspondence in `DCPO⊥!`.  This is still a concrete carrier-level statement;
comparison with arbitrary chosen internal-hom objects remains separate. -/
noncomputable def smashTensorHomOrderIsoData
    {D : Type u} {E : Type v} {F : Type w}
    [Preorder D] [Preorder E] [Preorder F] [OrderBot D] [OrderBot E]
    (hFdcpo : IsDcpo F) (hFanti : IsAntisymmetricOrder F)
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    OrderIsoData (StrictContFun (SmashProduct D E) F)
      (StrictContFun D (StrictContFun E F)) where
  toFun := StrictContFun.smashCurryBundled hDbot hEbot
  invFun := StrictContFun.smashUncurryBundled hFdcpo hDbot hEbot
  left_inv := StrictContFun.smashUncurry_smashCurryBundled hFdcpo hDbot hEbot
  right_inv := StrictContFun.smashCurry_smashUncurryBundled hFdcpo hFanti hDbot hEbot
  monotone_to := by
    intro f g hfg d e
    exact hfg (SmashProduct.mk (D := D) (E := E) d e)
  monotone_inv := by
    intro f g hfg z
    exact hfg (SmashProduct.toProd (D := D) (E := E) z).1
      (SmashProduct.toProd (D := D) (E := E) z).2

/-- The concrete smash tensor/function-space order isomorphism supplies the
tensor-hom support for `DCPO⊥!` in the current preorder interface. -/
theorem strictPointedTensorHomAdjunction :
    StrictPointedTensorHomAdjunction.{u} := by
  intro D E F _ _ _ _ _ _hDdcpo _hDanti _hDpointed _hEdcpo _hEanti _hEpointed
    hFdcpo hFanti _hFpointed hDbot hEbot
  exact ⟨StrictContFun.smashTensorHomOrderIsoData hFdcpo hFanti hDbot hEbot⟩

/-- The concrete strict function space and smash product supply the complete
local monoidal-closed interface. -/
theorem strictPointedDCPOMonoidalClosed :
    StrictPointedDCPOMonoidalClosed.{u} :=
  ⟨StrictContFun.strictPointedDCPOMonoidalClosedCore,
    StrictContFun.strictPointedTensorHomAdjunction⟩

/-- Compatibility theorem exposing both components of the monoidal-closed
interface. -/
theorem theorem_3_3_4_strict_pointed_dcpo_monoidal_closed_with_tensor_hom_concrete :
    StrictPointedDCPOMonoidalClosed.{u} :=
  StrictContFun.strictPointedDCPOMonoidalClosed

/-- Theorem 3.3.4: `DCPO⊥!` is monoidal closed, complete and cocomplete in
the chapter's concrete category interface.  Cocompleteness remains the
explicit book-omitted proof debt recorded above. -/
theorem theorem_3_3_4_strict_pointed_dcpo_monoidal_closed_complete_cocomplete :
    StrictPointedDCPOMonoidalClosed.{u} ∧
      StrictPointedDCPOHasAllLimits.{u, v, w, z} ∧
        StrictPointedDCPOHasAllColimits.{u, v, w, z} :=
  theorem_3_3_4_strict_pointed_dcpo_monoidal_closed_complete_cocomplete_of_monoidalClosed
    StrictContFun.strictPointedDCPOMonoidalClosed
    theorem_3_3_4_strict_pointed_dcpo_complete

end StrictContFun

namespace ContFun

/-- Evaluation of a directed family of continuous maps is directed pointwise. -/
theorem eval_directed
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    {A : Set (ContFun D E)} (hA : DirectedSet A) (d : D) :
    DirectedSet ((fun f : ContFun D E => f d) '' A) :=
  DirectedSet.image (f := fun f : ContFun D E => f d)
    (by intro f g hfg; exact hfg d) hA

/-- Pointwise supremum of a directed family of continuous maps. -/
noncomputable def directedSupFun
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (ContFun D E)) (hA : DirectedSet A) : D → E :=
  fun d => Classical.choose (hE ((fun f : ContFun D E => f d) '' A)
    (ContFun.eval_directed hA d))

/-- The pointwise value of `directedSupFun` is the supremum of the pointwise
evaluation set. -/
theorem directedSupFun_isSup_eval
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (ContFun D E)) (hA : DirectedSet A) (d : D) :
    IsSup ((fun f : ContFun D E => f d) '' A)
      (ContFun.directedSupFun hE A hA d) :=
  Classical.choose_spec (hE ((fun f : ContFun D E => f d) '' A)
    (ContFun.eval_directed hA d))

/-- The pointwise directed supremum of continuous maps is monotone. -/
theorem directedSupFun_monotone
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (ContFun D E)) (hA : DirectedSet A) :
    Monotone (ContFun.directedSupFun hE A hA) := by
  intro d e hde
  exact (ContFun.directedSupFun_isSup_eval hE A hA d).2
    (ContFun.directedSupFun hE A hA e) (by
      intro y hy
      rcases hy with ⟨f, hfA, rfl⟩
      exact le_trans (f.continuous.1 hde)
        ((ContFun.directedSupFun_isSup_eval hE A hA e).1 ⟨f, hfA, rfl⟩))

/-- The pointwise directed supremum of continuous maps is Scott-continuous. -/
theorem directedSupFun_scottContinuous
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (ContFun D E)) (hA : DirectedSet A) :
    ScottContinuous (ContFun.directedSupFun hE A hA) := by
  constructor
  · exact ContFun.directedSupFun_monotone hE A hA
  · intro B s hB hs
    constructor
    · intro y hy
      rcases hy with ⟨b, hb, rfl⟩
      exact ContFun.directedSupFun_monotone hE A hA (hs.1 hb)
    · intro y hy
      exact (ContFun.directedSupFun_isSup_eval hE A hA s).2 y (by
        intro z hz
        rcases hz with ⟨f, hfA, rfl⟩
        exact (f.continuous.2 hB hs).2 y (by
          intro fb hfb
          rcases hfb with ⟨b, hb, rfl⟩
          exact le_trans
            ((ContFun.directedSupFun_isSup_eval hE A hA b).1 ⟨f, hfA, rfl⟩)
            (hy ⟨b, hb, rfl⟩)))

/-- Directed supremum in the continuous function space. -/
noncomputable def directedSup
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (ContFun D E)) (hA : DirectedSet A) :
    ContFun D E where
  toFun := ContFun.directedSupFun hE A hA
  continuous := ContFun.directedSupFun_scottContinuous hE A hA

/-- The constructed pointwise continuous function is the supremum of the
directed family. -/
theorem directedSup_isSup
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (A : Set (ContFun D E)) (hA : DirectedSet A) :
    IsSup A (ContFun.directedSup hE A hA) := by
  constructor
  · intro f hfA x
    change f x ≤ ContFun.directedSupFun hE A hA x
    exact (ContFun.directedSupFun_isSup_eval hE A hA x).1 ⟨f, hfA, rfl⟩
  · intro g hg x
    change ContFun.directedSupFun hE A hA x ≤ g x
    exact (ContFun.directedSupFun_isSup_eval hE A hA x).2 (g x) (by
      intro y hy
      rcases hy with ⟨f, hfA, rfl⟩
      exact hg hfA x)

/-- If the codomain is a dcpo, then continuous maps into it form a dcpo under
the pointwise order. -/
theorem isDcpo_of_codomain
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) : IsDcpo (ContFun D E) := by
  intro A hA
  exact ⟨ContFun.directedSup hE A hA, ContFun.directedSup_isSup hE A hA⟩

/-- Extensionality for bundled continuous maps. -/
theorem ext_apply
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    {f g : ContFun D E} (h : ∀ x : D, f x = g x) : f = g := by
  cases f with
  | mk f hf =>
      cases g with
      | mk g hg =>
          have hfun : f = g := funext h
          subst hfun
          congr

/-- Evaluation at a point is Scott-continuous for the pointwise function-space
dcpo. -/
theorem eval_scottContinuous
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) (d : D) : ScottContinuous (fun f : ContFun D E => f d) := by
  constructor
  · intro f g hfg
    exact hfg d
  · intro A s hA hs
    constructor
    · intro y hy
      rcases hy with ⟨f, hfA, rfl⟩
      exact hs.1 hfA d
    · intro y hy
      have hPointSup : IsSup A (ContFun.directedSup hE A hA) :=
        ContFun.directedSup_isSup hE A hA
      exact le_trans ((hs.2 (ContFun.directedSup hE A hA) hPointSup.1) d)
        ((ContFun.directedSupFun_isSup_eval hE A hA d).2 y hy)

/-- The application map `[D -> E] × D -> E` is Scott-continuous. -/
theorem apply_scottContinuous
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsDcpo E) :
    ScottContinuous (ContFun.apply : ContFun D E × D → E) := by
  exact (lemma_3_2_6_continuous_iff_separately_continuous
    (ContFun.apply : ContFun D E × D → E)).2
    ⟨fun f => f.continuous, fun d => ContFun.eval_scottContinuous hE d⟩

/-- Bundled currying from continuous maps on a product into the continuous
function space. -/
def curryBundled
    {D : Type u} {E : Type v} {F : Type w} [Preorder D] [Preorder E] [Preorder F]
    (f : ContFun (D × E) F) : ContFun D (ContFun E F) where
  toFun := fun d =>
    { toFun := fun e => f (d, e)
      continuous :=
        (lemma_3_2_6_continuous_iff_separately_continuous
          (fun p : D × E => f p)).1 f.continuous |>.1 d }
  continuous := by
    have hsep : SeparatelyScottContinuous (fun p : D × E => f p) :=
      (lemma_3_2_6_continuous_iff_separately_continuous
        (fun p : D × E => f p)).1 f.continuous
    constructor
    · intro d e hde x
      exact f.continuous.1 ⟨hde, le_rfl⟩
    · intro A s hA hs
      constructor
      · intro y hy x
        rcases hy with ⟨d, hdA, rfl⟩
        exact f.continuous.1 ⟨hs.1 hdA, le_rfl⟩
      · intro g hg x
        have hxSup : IsSup ((fun d : D => f (d, x)) '' A) (f (s, x)) :=
          (hsep.2 x).2 hA hs
        exact hxSup.2 (g x) (by
          intro y hy
          rcases hy with ⟨d, hdA, rfl⟩
          exact hg ⟨d, hdA, rfl⟩ x)

/-- Uncurrying from the continuous function space back to maps on the product. -/
def uncurryBundled
    {D : Type u} {E : Type v} {F : Type w} [Preorder D] [Preorder E] [Preorder F]
    (hF : IsDcpo F) (g : ContFun D (ContFun E F)) : ContFun (D × E) F where
  toFun := fun p => g p.1 p.2
  continuous := by
    exact (lemma_3_2_6_continuous_iff_separately_continuous
      (fun p : D × E => g p.1 p.2)).2
      ⟨fun d => (g d).continuous,
        fun e => (ContFun.eval_scottContinuous hF e).comp g.continuous⟩

/-- Uncurrying is inverse to bundled currying. -/
theorem uncurry_curryBundled
    {D : Type u} {E : Type v} {F : Type w} [Preorder D] [Preorder E] [Preorder F]
    (hF : IsDcpo F) (f : ContFun (D × E) F) :
    ContFun.uncurryBundled hF (ContFun.curryBundled f) = f := by
  apply ContFun.ext_apply
  intro p
  cases p
  rfl

/-- Bundled currying is inverse to uncurrying. -/
theorem curry_uncurryBundled
    {D : Type u} {E : Type v} {F : Type w} [Preorder D] [Preorder E] [Preorder F]
    (hF : IsDcpo F) (g : ContFun D (ContFun E F)) :
    ContFun.curryBundled (ContFun.uncurryBundled hF g) = g := by
  apply ContFun.ext_apply
  intro d
  apply ContFun.ext_apply
  intro e
  rfl

/-- The concrete currying order-isomorphism supporting the cartesian-closed
function-space interpretation. -/
def curryOrderIsoData
    {D : Type u} {E : Type v} {F : Type w} [Preorder D] [Preorder E] [Preorder F]
    (hF : IsDcpo F) : OrderIsoData (ContFun (D × E) F) (ContFun D (ContFun E F)) where
  toFun := ContFun.curryBundled
  invFun := ContFun.uncurryBundled hF
  left_inv := ContFun.uncurry_curryBundled hF
  right_inv := ContFun.curry_uncurryBundled hF
  monotone_to := by
    intro f g hfg d e
    exact hfg (d, e)
  monotone_inv := by
    intro f g hfg p
    exact hfg p.1 p.2

/-- Concrete `DCPO` function-space adjunction supplied by application and
currying. -/
theorem dcpoFunctionSpaceAdjunction :
    DCPOFunctionSpaceAdjunction.{u} := by
  intro C D E _ _ _ _hCdcpo _hCanti _hDdcpo _hDanti hEdcpo _hEanti
  exact ⟨ContFun.curryOrderIsoData hEdcpo⟩

/-- The concrete ordinary continuous function space supplies the internal-hom
comparison for `DCPO`. -/
theorem dcpoInternalHomComparison :
    DCPOInternalHomComparison.{u} := by
  intro D E _ _ _hDdcpo _hDanti hEdcpo hEanti
  refine ⟨ContFun D E, inferInstance, ?_, ?_, ?_⟩
  · exact ContFun.isDcpo_of_codomain hEdcpo
  · exact ContFun.antisymmetric_of_codomain hEanti
  · exact ⟨OrderIsoData.refl (ContFun D E)⟩

/-- Build the current `DCPO` cartesian-closed interface once the remaining
internal-hom comparison is supplied. -/
theorem dcpoCartesianClosed_of_internalHomComparison
    (h : DCPOInternalHomComparison.{u}) : DCPOCartesianClosed.{u} :=
  ⟨ContFun.dcpoFunctionSpaceAdjunction, h⟩

/-- The concrete ordinary continuous function-space carrier makes `DCPO`
cartesian closed in the current interface. -/
theorem dcpoCartesianClosed : DCPOCartesianClosed.{u} :=
  ContFun.dcpoCartesianClosed_of_internalHomComparison
    ContFun.dcpoInternalHomComparison

/-- Concrete `DCPO⊥` function-space adjunction.  Morphisms are ordinary
Scott-continuous maps, so the proof is the same curry/uncurry construction as
for `DCPO`; the pointed object hypotheses are retained in the interface. -/
theorem pointedDCPOFunctionSpaceAdjunction :
    PointedDCPOFunctionSpaceAdjunction.{u} := by
  intro C D E _ _ _ _hCdcpo _hCanti _hCpointed
    _hDdcpo _hDanti _hDpointed hEdcpo _hEanti _hEpointed
  exact ⟨ContFun.curryOrderIsoData hEdcpo⟩

/-- The concrete ordinary continuous function space supplies the pointed
internal-hom comparison for `DCPO⊥`. -/
theorem pointedDCPOInternalHomComparison :
    PointedDCPOInternalHomComparison.{u} := by
  intro D E _ _ _hDdcpo _hDanti _hDpointed hEdcpo hEanti hEpointed
  refine ⟨ContFun D E, inferInstance, ?_, ?_, ?_, ?_⟩
  · exact ContFun.isDcpo_of_codomain hEdcpo
  · exact ContFun.antisymmetric_of_codomain hEanti
  · exact ContFun.hasLeastElement_of_codomain hEpointed
  · exact ⟨OrderIsoData.refl (ContFun D E)⟩

/-- Build the current `DCPO⊥` cartesian-closed interface once the remaining
pointed internal-hom comparison is supplied. -/
theorem pointedDCPOCartesianClosed_of_internalHomComparison
    (h : PointedDCPOInternalHomComparison.{u}) :
    PointedDCPOCartesianClosed.{u} :=
  ⟨ContFun.pointedDCPOFunctionSpaceAdjunction, h⟩

/-- The concrete ordinary continuous function-space carrier makes `DCPO⊥`
cartesian closed in the current interface. -/
theorem pointedDCPOCartesianClosed :
    PointedDCPOCartesianClosed.{u} :=
  ContFun.pointedDCPOCartesianClosed_of_internalHomComparison
    ContFun.pointedDCPOInternalHomComparison

end ContFun

/-- Theorem 3.3.3. PDF text: "DCPO is cartesian closed, complete and
cocomplete."

Current Lean spelling: in the local preorder-based interface, partial-order
dcpos with Scott-continuous morphisms are cartesian closed, complete, and
cocomplete.  Cartesian closedness is witnessed by the ordinary continuous
function-space carrier `ContFun D E`; cocompleteness is the documented external
theorem 3.3.2. -/
theorem theorem_3_3_3_dcpo_cartesian_closed_complete_cocomplete :
    DCPOCartesianClosed.{u} ∧ DCPOHasAllLimits.{u, v, w, z} ∧
      DCPOHasAllColimits.{u, v, w, z} :=
  theorem_3_3_3_dcpo_cartesian_closed_complete_cocomplete_of_cartesianClosed
    ContFun.dcpoCartesianClosed

/-- Theorem 3.3.5. PDF text: "DCPO⊥ is cartesian closed."

Current Lean spelling: in the local preorder-based interface, pointed dcpos
with ordinary Scott-continuous morphisms are cartesian closed.  The exponential
object is represented by the ordinary continuous function-space carrier
`ContFun D E`, with its pointwise dcpo, least element, and antisymmetric order
inherited from the codomain. -/
theorem theorem_3_3_5_pointed_dcpo_cartesian_closed :
    PointedDCPOCartesianClosed.{u} :=
  ContFun.pointedDCPOCartesianClosed


end Chapter3
end AbramskyJung

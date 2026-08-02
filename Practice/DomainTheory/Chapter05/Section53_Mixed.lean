import Practice.DomainTheory.Chapter05.Section53_Ordinary

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 5.3: Mixed Variance

Least mixed homomorphism pairs, mixed fixed-point invariance, minimality, and
free mixed-variant algebras.
-/

universe u

namespace AbramskyJung
namespace Chapter5

open Chapter4

/-- The ordered pair of continuous maps underlying a mixed homomorphism pair. -/
abbrev MixedHomMaps
    (F : MixedVariantFunctor.{u})
    (A B : MixedDomainEquationSolution F) :=
  OrderedDomain.ContFunCarrier A.object B.object ×
    OrderedDomain.ContFunCarrier B.object A.object

namespace MixedHomPair

/-- Reverse a mixed homomorphism pair by exchanging its two maps. -/
def reverse
    {F : MixedVariantFunctor.{u}} {A B : MixedDomainEquationSolution F}
    (p : MixedHomPair F A B) : MixedHomPair F B A where
  forward := p.backward
  backward := p.forward
  forward_commutes := p.backward_commutes
  backward_commutes := p.forward_commutes

/-- Composition of mixed homomorphism pairs. -/
def comp
    {F : MixedVariantFunctor.{u}} {A B C : MixedDomainEquationSolution F}
    (g : MixedHomPair F B C) (f : MixedHomPair F A B) :
    MixedHomPair F A C where
  forward := OrderedDomain.compContFun g.forward f.forward
  backward := OrderedDomain.compContFun f.backward g.backward
  forward_commutes := by
    intro x
    change g.forward (f.forward (A.fold x)) =
      C.fold
        (F.mapHom
          (OrderedDomain.compContFun f.backward g.backward)
          (OrderedDomain.compContFun g.forward f.forward) x)
    calc
      g.forward (f.forward (A.fold x)) =
          g.forward (B.fold (F.mapHom f.backward f.forward x)) := by
            rw [f.forward_commutes]
      _ = C.fold
          (F.mapHom g.backward g.forward
            (F.mapHom f.backward f.forward x)) := g.forward_commutes _
      _ = C.fold
          (F.mapHom
            (OrderedDomain.compContFun f.backward g.backward)
            (OrderedDomain.compContFun g.forward f.forward) x) := by
              rw [F.mapHom_comp]
  backward_commutes := by
    intro x
    change f.backward (g.backward (C.fold x)) =
      A.fold
        (F.mapHom
          (OrderedDomain.compContFun g.forward f.forward)
          (OrderedDomain.compContFun f.backward g.backward) x)
    calc
      f.backward (g.backward (C.fold x)) =
          f.backward (B.fold (F.mapHom g.forward g.backward x)) := by
            rw [g.backward_commutes]
      _ = A.fold
          (F.mapHom f.forward f.backward
            (F.mapHom g.forward g.backward x)) := f.backward_commutes _
      _ = A.fold
          (F.mapHom
            (OrderedDomain.compContFun g.forward f.forward)
            (OrderedDomain.compContFun f.backward g.backward) x) := by
              rw [F.mapHom_comp]

end MixedHomPair

/-- Pointwise antisymmetry for the ordered space underlying mixed homomorphism
pairs. -/
theorem mixedHomMaps_antisymm
    (F : MixedVariantFunctor.{u})
    (A B : MixedDomainEquationSolution F)
    (hAanti : ∀ x y : A.object.carrier, x ≤ y → y ≤ x → x = y)
    (hBanti : ∀ x y : B.object.carrier, x ≤ y → y ≤ x → x = y) :
    ∀ p q : MixedHomMaps F A B, p ≤ q → q ≤ p → p = q := by
  intro p q hpq hqp
  apply Prod.ext
  · apply Chapter3.ContFun.ext_apply
    intro x
    exact hBanti _ _ (hpq.1 x) (hqp.1 x)
  · apply Chapter3.ContFun.ext_apply
    intro x
    exact hAanti _ _ (hpq.2 x) (hqp.2 x)

/-- Simultaneous homomorphism functional used in Lemma 5.3.6. -/
def mixedHomFunctional
    (F : MixedVariantFunctor.{u})
    (A B : MixedDomainEquationSolution F)
    (p : MixedHomMaps F A B) : MixedHomMaps F A B :=
  (OrderedDomain.compContFun B.fold
      (OrderedDomain.compContFun (F.mapHom p.2 p.1) A.unfold),
    OrderedDomain.compContFun A.fold
      (OrderedDomain.compContFun (F.mapHom p.1 p.2) B.unfold))

/-- Local continuity of a mixed functor makes its simultaneous homomorphism
functional Scott-continuous. -/
theorem mixedHomFunctional_scottContinuous
    (F : MixedVariantFunctor.{u})
    (hF : def_5_2_5_mixed_variant_functor F)
    (A B : MixedDomainEquationSolution F)
    (hFAA : Chapter3.IsDcpo (F.mapObj A.object A.object).carrier)
    (hFBB : Chapter3.IsDcpo (F.mapObj B.object B.object).carrier) :
    Chapter3.ScottContinuous (mixedHomFunctional F A B) := by
  let swap :
      OrderedDomain.ContFunCarrier A.object B.object ×
          OrderedDomain.ContFunCarrier B.object A.object →
        OrderedDomain.ContFunCarrier B.object A.object ×
          OrderedDomain.ContFunCarrier A.object B.object :=
    fun p => (p.2, p.1)
  have hswap : Chapter3.ScottContinuous swap :=
    Chapter3.prod_pair_scottContinuous Chapter3.prod_snd_scottContinuous
      Chapter3.prod_fst_scottContinuous
  have hMapAB : Chapter3.ScottContinuous
      (fun p : OrderedDomain.ContFunCarrier A.object B.object ×
          OrderedDomain.ContFunCarrier B.object A.object =>
        F.mapHom p.2 p.1) :=
    Chapter3.ScottContinuous.comp
      (hF.hom_continuous
        (D₁ := A.object) (D₂ := B.object)
        (E₁ := A.object) (E₂ := B.object)) hswap
  have hMapBA : Chapter3.ScottContinuous
      (fun p : OrderedDomain.ContFunCarrier A.object B.object ×
          OrderedDomain.ContFunCarrier B.object A.object =>
        F.mapHom p.1 p.2) :=
    hF.hom_continuous
      (D₁ := B.object) (D₂ := A.object)
      (E₁ := B.object) (E₂ := A.object)
  apply Chapter3.prod_pair_scottContinuous
  · exact Chapter3.ScottContinuous.comp
      (f := fun q : OrderedDomain.ContFunCarrier
          (F.mapObj A.object A.object) (F.mapObj B.object B.object) =>
        OrderedDomain.compContFun B.fold (OrderedDomain.compContFun q A.unfold))
      (g := fun p : OrderedDomain.ContFunCarrier A.object B.object ×
          OrderedDomain.ContFunCarrier B.object A.object =>
        F.mapHom p.2 p.1)
      (whisker_scottContinuous A.object (F.mapObj A.object A.object)
        (F.mapObj B.object B.object) B.object hFBB A.unfold B.fold)
      hMapAB
  · exact Chapter3.ScottContinuous.comp
      (f := fun q : OrderedDomain.ContFunCarrier
          (F.mapObj B.object B.object) (F.mapObj A.object A.object) =>
        OrderedDomain.compContFun A.fold (OrderedDomain.compContFun q B.unfold))
      (g := fun p : OrderedDomain.ContFunCarrier A.object B.object ×
          OrderedDomain.ContFunCarrier B.object A.object =>
        F.mapHom p.1 p.2)
      (whisker_scottContinuous B.object (F.mapObj B.object B.object)
        (F.mapObj A.object A.object) A.object hFAA B.unfold A.fold)
      hMapBA

/-- Compose two pairs of underlying maps in the variance-correct order. -/
def composeMixedHomMaps
    (F : MixedVariantFunctor.{u})
    (A B C : MixedDomainEquationSolution F)
    (p : MixedHomMaps F A B × MixedHomMaps F B C) :
    MixedHomMaps F A C :=
  (OrderedDomain.compContFun p.2.1 p.1.1,
    OrderedDomain.compContFun p.1.2 p.2.2)

/-- Composition of mixed map pairs is jointly Scott-continuous. -/
theorem composeMixedHomMaps_scottContinuous
    (F : MixedVariantFunctor.{u})
    (A B C : MixedDomainEquationSolution F)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hBdcpo : Chapter3.IsDcpo B.object.carrier)
    (hCdcpo : Chapter3.IsDcpo C.object.carrier) :
    Chapter3.ScottContinuous (composeMixedHomMaps F A B C) := by
  have hForwardInput : Chapter3.ScottContinuous
      (fun p : MixedHomMaps F A B × MixedHomMaps F B C => (p.2.1, p.1.1)) :=
    Chapter3.prod_pair_scottContinuous
      (Chapter3.ScottContinuous.comp Chapter3.prod_fst_scottContinuous
        Chapter3.prod_snd_scottContinuous)
      (Chapter3.ScottContinuous.comp Chapter3.prod_fst_scottContinuous
        Chapter3.prod_fst_scottContinuous)
  have hBackwardInput : Chapter3.ScottContinuous
      (fun p : MixedHomMaps F A B × MixedHomMaps F B C => (p.1.2, p.2.2)) :=
    Chapter3.prod_pair_scottContinuous
      (Chapter3.ScottContinuous.comp Chapter3.prod_snd_scottContinuous
        Chapter3.prod_fst_scottContinuous)
      (Chapter3.ScottContinuous.comp Chapter3.prod_snd_scottContinuous
        Chapter3.prod_snd_scottContinuous)
  exact Chapter3.prod_pair_scottContinuous
    (Chapter3.ScottContinuous.comp
      (composition_scottContinuous A.object B.object C.object
        hBdcpo hCdcpo)
      hForwardInput)
    (Chapter3.ScottContinuous.comp
      (composition_scottContinuous C.object B.object A.object
        hBdcpo hAdcpo)
      hBackwardInput)

/-- Apply the two simultaneous homomorphism functionals componentwise. -/
def mixedHomFunctionalProduct
    (F : MixedVariantFunctor.{u})
    (A B C : MixedDomainEquationSolution F)
    (p : MixedHomMaps F A B × MixedHomMaps F B C) :
    MixedHomMaps F A B × MixedHomMaps F B C :=
  (mixedHomFunctional F A B p.1, mixedHomFunctional F B C p.2)

/-- The product of two mixed homomorphism functionals is Scott-continuous. -/
theorem mixedHomFunctionalProduct_scottContinuous
    (F : MixedVariantFunctor.{u})
    (hF : def_5_2_5_mixed_variant_functor F)
    (A B C : MixedDomainEquationSolution F)
    (hFAA : Chapter3.IsDcpo (F.mapObj A.object A.object).carrier)
    (hFBB : Chapter3.IsDcpo (F.mapObj B.object B.object).carrier)
    (hFCC : Chapter3.IsDcpo (F.mapObj C.object C.object).carrier) :
    Chapter3.ScottContinuous (mixedHomFunctionalProduct F A B C) := by
  exact Chapter3.prod_pair_scottContinuous
    (Chapter3.ScottContinuous.comp
      (mixedHomFunctional_scottContinuous F hF A B hFAA hFBB)
      Chapter3.prod_fst_scottContinuous)
    (Chapter3.ScottContinuous.comp
      (mixedHomFunctional_scottContinuous F hF B C hFBB hFCC)
      Chapter3.prod_snd_scottContinuous)

/-- Mixed-map composition intertwines the product functional with the
functional for the composite source and target. -/
theorem composeMixedHomMaps_functional
    (F : MixedVariantFunctor.{u})
    (A B C : MixedDomainEquationSolution F)
    (p : MixedHomMaps F A B × MixedHomMaps F B C) :
    composeMixedHomMaps F A B C (mixedHomFunctionalProduct F A B C p) =
      mixedHomFunctional F A C (composeMixedHomMaps F A B C p) := by
  apply Prod.ext
  · apply Chapter3.ContFun.ext_apply
    intro x
    change C.fold
        (F.mapHom p.2.2 p.2.1
          (B.unfold (B.fold (F.mapHom p.1.2 p.1.1 (A.unfold x))))) =
      C.fold
        (F.mapHom
          (OrderedDomain.compContFun p.1.2 p.2.2)
          (OrderedDomain.compContFun p.2.1 p.1.1)
          (A.unfold x))
    rw [B.unfold_fold, F.mapHom_comp]
  · apply Chapter3.ContFun.ext_apply
    intro x
    change A.fold
        (F.mapHom p.1.1 p.1.2
          (B.unfold (B.fold (F.mapHom p.2.1 p.2.2 (C.unfold x))))) =
      A.fold
        (F.mapHom
          (OrderedDomain.compContFun p.2.1 p.1.1)
          (OrderedDomain.compContFun p.1.2 p.2.2)
          (C.unfold x))
    rw [B.unfold_fold, F.mapHom_comp]

/-- The simultaneous homomorphism functional as a bundled continuous endomap. -/
def mixedHomFunctionalContFun
    (F : MixedVariantFunctor.{u})
    (hF : def_5_2_5_mixed_variant_functor F)
    (A B : MixedDomainEquationSolution F)
    (hFAA : Chapter3.IsDcpo (F.mapObj A.object A.object).carrier)
    (hFBB : Chapter3.IsDcpo (F.mapObj B.object B.object).carrier) :
    Chapter3.ContFun
      (OrderedDomain.ContFunCarrier A.object B.object ×
        OrderedDomain.ContFunCarrier B.object A.object)
      (OrderedDomain.ContFunCarrier A.object B.object ×
        OrderedDomain.ContFunCarrier B.object A.object) where
  toFun := mixedHomFunctional F A B
  continuous := mixedHomFunctional_scottContinuous F hF A B hFAA hFBB

/-- The least simultaneous fixed point underlying Lemma 5.3.6. -/
noncomputable def leastMixedHomMaps
    (F : MixedVariantFunctor.{u})
    (hF : def_5_2_5_mixed_variant_functor F)
    (A B : MixedDomainEquationSolution F)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hBdcpo : Chapter3.IsDcpo B.object.carrier)
    (hFAA : Chapter3.IsDcpo (F.mapObj A.object A.object).carrier)
    (hFBB : Chapter3.IsDcpo (F.mapObj B.object B.object).carrier)
    [OrderBot A.object.carrier] [OrderBot B.object.carrier] :
    OrderedDomain.ContFunCarrier A.object B.object ×
      OrderedDomain.ContFunCarrier B.object A.object :=
  preorderChosenLeastFix
    (Chapter3.prod_isDcpo
      (Chapter3.ContFun.isDcpo_of_codomain hBdcpo)
      (Chapter3.ContFun.isDcpo_of_codomain hAdcpo))
    (mixedHomFunctionalContFun F hF A B hFAA hFBB)

/-- Fixed-point and leastness specification for `leastMixedHomMaps`. -/
theorem leastMixedHomMaps_spec
    (F : MixedVariantFunctor.{u})
    (hF : def_5_2_5_mixed_variant_functor F)
    (A B : MixedDomainEquationSolution F)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hAanti : ∀ x y : A.object.carrier, x ≤ y → y ≤ x → x = y)
    (hBdcpo : Chapter3.IsDcpo B.object.carrier)
    (hBanti : ∀ x y : B.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFAA : Chapter3.IsDcpo (F.mapObj A.object A.object).carrier)
    (hFBB : Chapter3.IsDcpo (F.mapObj B.object B.object).carrier)
    [OrderBot A.object.carrier] [OrderBot B.object.carrier] :
    mixedHomFunctional F A B
        (leastMixedHomMaps F hF A B hAdcpo hBdcpo hFAA hFBB) =
      leastMixedHomMaps F hF A B hAdcpo hBdcpo hFAA hFBB ∧
    ∀ p : OrderedDomain.ContFunCarrier A.object B.object ×
        OrderedDomain.ContFunCarrier B.object A.object,
      mixedHomFunctional F A B p = p →
        leastMixedHomMaps F hF A B hAdcpo hBdcpo hFAA hFBB ≤ p := by
  have hAnti : ∀ p q :
      OrderedDomain.ContFunCarrier A.object B.object ×
        OrderedDomain.ContFunCarrier B.object A.object,
      p ≤ q → q ≤ p → p = q := by
    intro p q hpq hqp
    apply Prod.ext
    · apply Chapter3.ContFun.ext_apply
      intro x
      exact hBanti _ _ (hpq.1 x) (hqp.1 x)
    · apply Chapter3.ContFun.ext_apply
      intro x
      exact hAanti _ _ (hpq.2 x) (hqp.2 x)
  exact preorderChosenLeastFix_spec
    (Chapter3.prod_isDcpo
      (Chapter3.ContFun.isDcpo_of_codomain hBdcpo)
      (Chapter3.ContFun.isDcpo_of_codomain hAdcpo)) hAnti
    (mixedHomFunctionalContFun F hF A B hFAA hFBB)

/-- The least simultaneous fixed points compose.  This is the fixed-point
calculation underlying the composition clause of Lemma 5.3.6. -/
theorem leastMixedHomMaps_composition
    (F : MixedVariantFunctor.{u})
    (hF : def_5_2_5_mixed_variant_functor F)
    (A B C : MixedDomainEquationSolution F)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hAanti : ∀ x y : A.object.carrier, x ≤ y → y ≤ x → x = y)
    (hBdcpo : Chapter3.IsDcpo B.object.carrier)
    (hBanti : ∀ x y : B.object.carrier, x ≤ y → y ≤ x → x = y)
    (hCdcpo : Chapter3.IsDcpo C.object.carrier)
    (hCanti : ∀ x y : C.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFAA : Chapter3.IsDcpo (F.mapObj A.object A.object).carrier)
    (hFBB : Chapter3.IsDcpo (F.mapObj B.object B.object).carrier)
    (hFCC : Chapter3.IsDcpo (F.mapObj C.object C.object).carrier)
    [OrderBot A.object.carrier] [OrderBot B.object.carrier]
    [OrderBot C.object.carrier] :
    leastMixedHomMaps F hF A C hAdcpo hCdcpo hFAA hFCC =
      composeMixedHomMaps F A B C
        (leastMixedHomMaps F hF A B hAdcpo hBdcpo hFAA hFBB,
          leastMixedHomMaps F hF B C hBdcpo hCdcpo hFBB hFCC) := by
  letI hABForwardOrderBot : OrderBot
      (OrderedDomain.ContFunCarrier A.object B.object) :=
    { bot := Chapter3.ContFun.const (⊥ : B.object.carrier)
      bot_le := fun _ _ => bot_le }
  letI hABBackwardOrderBot : OrderBot
      (OrderedDomain.ContFunCarrier B.object A.object) :=
    { bot := Chapter3.ContFun.const (⊥ : A.object.carrier)
      bot_le := fun _ _ => bot_le }
  letI hBCForwardOrderBot : OrderBot
      (OrderedDomain.ContFunCarrier B.object C.object) :=
    { bot := Chapter3.ContFun.const (⊥ : C.object.carrier)
      bot_le := fun _ _ => bot_le }
  letI hBCBackwardOrderBot : OrderBot
      (OrderedDomain.ContFunCarrier C.object B.object) :=
    { bot := Chapter3.ContFun.const (⊥ : B.object.carrier)
      bot_le := fun _ _ => bot_le }
  letI hACForwardOrderBot : OrderBot
      (OrderedDomain.ContFunCarrier A.object C.object) :=
    { bot := Chapter3.ContFun.const (⊥ : C.object.carrier)
      bot_le := fun _ _ => bot_le }
  letI hACBackwardOrderBot : OrderBot
      (OrderedDomain.ContFunCarrier C.object A.object) :=
    { bot := Chapter3.ContFun.const (⊥ : A.object.carrier)
      bot_le := fun _ _ => bot_le }
  letI hABOrderBot : OrderBot (MixedHomMaps F A B) :=
    { bot := (⊥, ⊥)
      bot_le := fun p => ⟨bot_le, bot_le⟩ }
  letI hBCOrderBot : OrderBot (MixedHomMaps F B C) :=
    { bot := (⊥, ⊥)
      bot_le := fun p => ⟨bot_le, bot_le⟩ }
  letI hACOrderBot : OrderBot (MixedHomMaps F A C) :=
    { bot := (⊥, ⊥)
      bot_le := fun p => ⟨bot_le, bot_le⟩ }
  letI hProductOrderBot : OrderBot
      (MixedHomMaps F A B × MixedHomMaps F B C) :=
    { bot := (⊥, ⊥)
      bot_le := fun p => ⟨bot_le, bot_le⟩ }
  let hABdcpo : Chapter3.IsDcpo (MixedHomMaps F A B) :=
    Chapter3.prod_isDcpo
      (Chapter3.ContFun.isDcpo_of_codomain hBdcpo)
      (Chapter3.ContFun.isDcpo_of_codomain hAdcpo)
  let hBCdcpo : Chapter3.IsDcpo (MixedHomMaps F B C) :=
    Chapter3.prod_isDcpo
      (Chapter3.ContFun.isDcpo_of_codomain hCdcpo)
      (Chapter3.ContFun.isDcpo_of_codomain hBdcpo)
  let hACdcpo : Chapter3.IsDcpo (MixedHomMaps F A C) :=
    Chapter3.prod_isDcpo
      (Chapter3.ContFun.isDcpo_of_codomain hCdcpo)
      (Chapter3.ContFun.isDcpo_of_codomain hAdcpo)
  let hProductDcpo : Chapter3.IsDcpo
      (MixedHomMaps F A B × MixedHomMaps F B C) :=
    Chapter3.prod_isDcpo hABdcpo hBCdcpo
  let phiProduct : Chapter3.ContFun
      (MixedHomMaps F A B × MixedHomMaps F B C)
      (MixedHomMaps F A B × MixedHomMaps F B C) :=
    { toFun := mixedHomFunctionalProduct F A B C
      continuous := mixedHomFunctionalProduct_scottContinuous
        F hF A B C hFAA hFBB hFCC }
  let phiAC : Chapter3.ContFun (MixedHomMaps F A C) (MixedHomMaps F A C) :=
    mixedHomFunctionalContFun F hF A C hFAA hFCC
  let composeMaps : Chapter3.ContFun
      (MixedHomMaps F A B × MixedHomMaps F B C) (MixedHomMaps F A C) :=
    { toFun := composeMixedHomMaps F A B C
      continuous := composeMixedHomMaps_scottContinuous
        F A B C hAdcpo hBdcpo hCdcpo }
  have hABanti := mixedHomMaps_antisymm F A B hAanti hBanti
  have hBCanti := mixedHomMaps_antisymm F B C hBanti hCanti
  have hACanti := mixedHomMaps_antisymm F A C hAanti hCanti
  have hProductAnti : ∀ p q : MixedHomMaps F A B × MixedHomMaps F B C,
      p ≤ q → q ≤ p → p = q := by
    intro p q hpq hqp
    apply Prod.ext
    · exact hABanti _ _ hpq.1 hqp.1
    · exact hBCanti _ _ hpq.2 hqp.2
  have hComposeStrict : composeMaps ⊥ = ⊥ := by
    apply Prod.ext
    · apply Chapter3.ContFun.ext_apply
      intro x
      rfl
    · apply Chapter3.ContFun.ext_apply
      intro x
      rfl
  have hComposeComm : ∀ p : MixedHomMaps F A B × MixedHomMaps F B C,
      composeMaps (phiProduct p) = phiAC (composeMaps p) := by
    exact composeMixedHomMaps_functional F A B C
  have hInvariant := preorderChosenLeastFix_invariance
    (D := MixedHomMaps F A B × MixedHomMaps F B C)
    (E := MixedHomMaps F A C)
    hProductDcpo hACdcpo hACanti phiProduct phiAC composeMaps
      hComposeStrict hComposeComm
  let leastAB := leastMixedHomMaps F hF A B hAdcpo hBdcpo hFAA hFBB
  let leastBC := leastMixedHomMaps F hF B C hBdcpo hCdcpo hFBB hFCC
  let leastProduct := preorderChosenLeastFix hProductDcpo phiProduct
  have hABspec := leastMixedHomMaps_spec
    F hF A B hAdcpo hAanti hBdcpo hBanti hFAA hFBB
  have hBCspec := leastMixedHomMaps_spec
    F hF B C hBdcpo hBanti hCdcpo hCanti hFBB hFCC
  have hProductSpec := preorderChosenLeastFix_spec
    hProductDcpo hProductAnti phiProduct
  have hCandidateFix : phiProduct (leastAB, leastBC) = (leastAB, leastBC) := by
    apply Prod.ext
    · exact hABspec.1
    · exact hBCspec.1
  have hLeastProductLe : leastProduct ≤ (leastAB, leastBC) :=
    hProductSpec.2 (leastAB, leastBC) hCandidateFix
  have hLeastProductFix : phiProduct leastProduct = leastProduct := hProductSpec.1
  have hCandidateLe : (leastAB, leastBC) ≤ leastProduct := by
    constructor
    · exact hABspec.2 leastProduct.1 (congrArg Prod.fst hLeastProductFix)
    · exact hBCspec.2 leastProduct.2 (congrArg Prod.snd hLeastProductFix)
  have hLeastProductEq : leastProduct = (leastAB, leastBC) :=
    hProductAnti _ _ hLeastProductLe hCandidateLe
  change leastMixedHomMaps F hF A C hAdcpo hCdcpo hFAA hFCC =
    composeMixedHomMaps F A B C (leastAB, leastBC)
  change preorderChosenLeastFix hACdcpo phiAC =
    composeMaps (leastAB, leastBC)
  calc
    preorderChosenLeastFix hACdcpo phiAC = composeMaps leastProduct := hInvariant
    _ = composeMaps (leastAB, leastBC) := by rw [hLeastProductEq]

/-- Bundle the least simultaneous fixed point as a mixed homomorphism pair. -/
noncomputable def leastMixedHomPair
    (F : MixedVariantFunctor.{u})
    (hF : def_5_2_5_mixed_variant_functor F)
    (A B : MixedDomainEquationSolution F)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hAanti : ∀ x y : A.object.carrier, x ≤ y → y ≤ x → x = y)
    (hBdcpo : Chapter3.IsDcpo B.object.carrier)
    (hBanti : ∀ x y : B.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFAA : Chapter3.IsDcpo (F.mapObj A.object A.object).carrier)
    (hFBB : Chapter3.IsDcpo (F.mapObj B.object B.object).carrier)
    [OrderBot A.object.carrier] [OrderBot B.object.carrier] :
    MixedHomPair F A B where
  forward := (leastMixedHomMaps F hF A B hAdcpo hBdcpo hFAA hFBB).1
  backward := (leastMixedHomMaps F hF A B hAdcpo hBdcpo hFAA hFBB).2
  forward_commutes := by
    intro x
    have hfix :=
      (leastMixedHomMaps_spec F hF A B hAdcpo hAanti hBdcpo hBanti hFAA hFBB).1
    have hx := congrArg (fun p => p.1 (A.fold x)) hfix
    change B.fold (F.mapHom
        (leastMixedHomMaps F hF A B hAdcpo hBdcpo hFAA hFBB).2
        (leastMixedHomMaps F hF A B hAdcpo hBdcpo hFAA hFBB).1
        (A.unfold (A.fold x))) =
      (leastMixedHomMaps F hF A B hAdcpo hBdcpo hFAA hFBB).1 (A.fold x) at hx
    rw [A.unfold_fold] at hx
    exact hx.symm
  backward_commutes := by
    intro x
    have hfix :=
      (leastMixedHomMaps_spec F hF A B hAdcpo hAanti hBdcpo hBanti hFAA hFBB).1
    have hx := congrArg (fun p => p.2 (B.fold x)) hfix
    change A.fold (F.mapHom
        (leastMixedHomMaps F hF A B hAdcpo hBdcpo hFAA hFBB).1
        (leastMixedHomMaps F hF A B hAdcpo hBdcpo hFAA hFBB).2
        (B.unfold (B.fold x))) =
      (leastMixedHomMaps F hF A B hAdcpo hBdcpo hFAA hFBB).2 (B.fold x) at hx
    rw [B.unfold_fold] at hx
    exact hx.symm

/-- The bundled least mixed homomorphism pair is below every other pair. -/
theorem leastMixedHomPair_isLeast
    (F : MixedVariantFunctor.{u})
    (hF : def_5_2_5_mixed_variant_functor F)
    (A B : MixedDomainEquationSolution F)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hAanti : ∀ x y : A.object.carrier, x ≤ y → y ≤ x → x = y)
    (hBdcpo : Chapter3.IsDcpo B.object.carrier)
    (hBanti : ∀ x y : B.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFAA : Chapter3.IsDcpo (F.mapObj A.object A.object).carrier)
    (hFBB : Chapter3.IsDcpo (F.mapObj B.object B.object).carrier)
    [OrderBot A.object.carrier] [OrderBot B.object.carrier] :
    IsLeastMixedHomPair F A B
      (leastMixedHomPair F hF A B hAdcpo hAanti hBdcpo hBanti hFAA hFBB) := by
  intro q
  have hqfix : mixedHomFunctional F A B (q.forward, q.backward) =
      (q.forward, q.backward) := by
    apply Prod.ext
    · apply Chapter3.ContFun.ext_apply
      intro x
      change B.fold (F.mapHom q.backward q.forward (A.unfold x)) = q.forward x
      calc
        B.fold (F.mapHom q.backward q.forward (A.unfold x)) =
            q.forward (A.fold (A.unfold x)) := (q.forward_commutes (A.unfold x)).symm
        _ = q.forward x := by rw [A.fold_unfold]
    · apply Chapter3.ContFun.ext_apply
      intro x
      change A.fold (F.mapHom q.forward q.backward (B.unfold x)) = q.backward x
      calc
        A.fold (F.mapHom q.forward q.backward (B.unfold x)) =
            q.backward (B.fold (B.unfold x)) := (q.backward_commutes (B.unfold x)).symm
        _ = q.backward x := by rw [B.fold_unfold]
  exact (leastMixedHomMaps_spec F hF A B hAdcpo hAanti hBdcpo hBanti hFAA hFBB).2
    (q.forward, q.backward) hqfix

/-- Lemma 5.3.6, least mixed hom-pair component.  PDF text: for a mixed-variant
locally continuous functor and isomorphisms `i : F(A,A) -> A` and
`j : F(B,B) -> B`, there is a least pair of maps making the two diagrams
commute.

This remains direct proof debt until the least pair is constructed from the
locally continuous endomorphism functional. -/
theorem lemma_5_3_6_mixed_variant_mediating
    (F : MixedVariantFunctor.{u}) (hF : def_5_2_5_mixed_variant_functor F)
    (A B : MixedDomainEquationSolution F)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hAanti : ∀ x y : A.object.carrier, x ≤ y → y ≤ x → x = y)
    (hBdcpo : Chapter3.IsDcpo B.object.carrier)
    (hBanti : ∀ x y : B.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFAA : Chapter3.IsDcpo (F.mapObj A.object A.object).carrier)
    (hFBB : Chapter3.IsDcpo (F.mapObj B.object B.object).carrier)
    [OrderBot A.object.carrier] [OrderBot B.object.carrier] :
    ∃ p : MixedHomPair F A B, IsLeastMixedHomPair F A B p := by
  exact ⟨leastMixedHomPair F hF A B hAdcpo hAanti hBdcpo hBanti hFAA hFBB,
    leastMixedHomPair_isLeast F hF A B hAdcpo hAanti hBdcpo hBanti hFAA hFBB⟩

/-- Lemma 5.3.6, composition component.  PDF text: the composition of two least
mixed hom-pairs gives another least mixed hom-pair. -/
theorem lemma_5_3_6_mixed_hom_pair_composition
    (F : MixedVariantFunctor.{u}) (hF : def_5_2_5_mixed_variant_functor F)
    (A B C : MixedDomainEquationSolution F)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hAanti : ∀ x y : A.object.carrier, x ≤ y → y ≤ x → x = y)
    (hBdcpo : Chapter3.IsDcpo B.object.carrier)
    (hBanti : ∀ x y : B.object.carrier, x ≤ y → y ≤ x → x = y)
    (hCdcpo : Chapter3.IsDcpo C.object.carrier)
    (hCanti : ∀ x y : C.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFAA : Chapter3.IsDcpo (F.mapObj A.object A.object).carrier)
    (hFBB : Chapter3.IsDcpo (F.mapObj B.object B.object).carrier)
    (hFCC : Chapter3.IsDcpo (F.mapObj C.object C.object).carrier)
    [OrderBot A.object.carrier] [OrderBot B.object.carrier]
    [OrderBot C.object.carrier]
    (pAB : MixedHomPair F A B)
    (pBC : MixedHomPair F B C)
    (pAC : MixedHomPair F A C)
    (hAB : IsLeastMixedHomPair F A B pAB)
    (hBC : IsLeastMixedHomPair F B C pBC)
    (hForward : pAC.forward = OrderedDomain.compContFun pBC.forward pAB.forward)
    (hBackward : pAC.backward = OrderedDomain.compContFun pAB.backward pBC.backward) :
    IsLeastMixedHomPair F A C pAC := by
  let canonicalAB := leastMixedHomPair F hF A B
    hAdcpo hAanti hBdcpo hBanti hFAA hFBB
  let canonicalBC := leastMixedHomPair F hF B C
    hBdcpo hBanti hCdcpo hCanti hFBB hFCC
  let canonicalAC := leastMixedHomPair F hF A C
    hAdcpo hAanti hCdcpo hCanti hFAA hFCC
  have hCanonicalAB := leastMixedHomPair_isLeast F hF A B
    hAdcpo hAanti hBdcpo hBanti hFAA hFBB
  have hCanonicalBC := leastMixedHomPair_isLeast F hF B C
    hBdcpo hBanti hCdcpo hCanti hFBB hFCC
  have hCanonicalAC := leastMixedHomPair_isLeast F hF A C
    hAdcpo hAanti hCdcpo hCanti hFAA hFCC
  have hABForward : pAB.forward = canonicalAB.forward := by
    apply Chapter3.ContFun.ext_apply
    intro x
    exact hBanti _ _ (((hAB canonicalAB).1) x) (((hCanonicalAB pAB).1) x)
  have hABBackward : pAB.backward = canonicalAB.backward := by
    apply Chapter3.ContFun.ext_apply
    intro x
    exact hAanti _ _ (((hAB canonicalAB).2) x) (((hCanonicalAB pAB).2) x)
  have hBCForward : pBC.forward = canonicalBC.forward := by
    apply Chapter3.ContFun.ext_apply
    intro x
    exact hCanti _ _ (((hBC canonicalBC).1) x) (((hCanonicalBC pBC).1) x)
  have hBCBackward : pBC.backward = canonicalBC.backward := by
    apply Chapter3.ContFun.ext_apply
    intro x
    exact hBanti _ _ (((hBC canonicalBC).2) x) (((hCanonicalBC pBC).2) x)
  have hMapsComposition := leastMixedHomMaps_composition F hF A B C
    hAdcpo hAanti hBdcpo hBanti hCdcpo hCanti hFAA hFBB hFCC
  have hACForward : pAC.forward = canonicalAC.forward := by
    calc
      pAC.forward = OrderedDomain.compContFun pBC.forward pAB.forward := hForward
      _ = OrderedDomain.compContFun canonicalBC.forward canonicalAB.forward := by
        rw [hBCForward, hABForward]
      _ = canonicalAC.forward := (congrArg Prod.fst hMapsComposition).symm
  have hACBackward : pAC.backward = canonicalAC.backward := by
    calc
      pAC.backward = OrderedDomain.compContFun pAB.backward pBC.backward := hBackward
      _ = OrderedDomain.compContFun canonicalAB.backward canonicalBC.backward := by
        rw [hABBackward, hBCBackward]
      _ = canonicalAC.backward := (congrArg Prod.snd hMapsComposition).symm
  intro q
  constructor
  · rw [hACForward]
    exact (hCanonicalAC q).1
  · rw [hACBackward]
    exact (hCanonicalAC q).2

/-- A mixed endomorphism is exactly a fixed point of the mixed endomorphism
functional. -/
theorem mixedEndomorphism_iff_functional_fixpoint
    (F : MixedVariantFunctor.{u}) (A : MixedDomainEquationSolution F)
    (h : OrderedDomain.ContFunCarrier A.object A.object) :
    IsMixedEndomorphism F A h ↔ mixedEndomorphismFunctional F A h = h := by
  constructor
  · intro hh
    apply Chapter3.ContFun.ext_apply
    intro x
    calc
      mixedEndomorphismFunctional F A h x =
          A.fold (F.mapHom h h (A.unfold x)) := rfl
      _ = h (A.fold (A.unfold x)) := (hh (A.unfold x)).symm
      _ = h x := by rw [A.fold_unfold]
  · intro hfix x
    have hx := congrArg (fun k => k (A.fold x)) hfix
    change A.fold (F.mapHom h h (A.unfold (A.fold x))) = h (A.fold x) at hx
    rw [A.unfold_fold] at hx
    exact hx.symm

/-- Clauses (2) and (3) of Theorem 5.3.7 are equivalent without the
canonical-chain part of the invariance proof. -/
theorem identityLeastMixedEndomorphism_iff_identityLeastMixedFunctionalFixpoint
    (F : MixedVariantFunctor.{u}) (A : MixedDomainEquationSolution F) :
    IdentityIsLeastMixedEndomorphism F A ↔
      IdentityIsLeastMixedFunctionalFixpoint F A := by
  constructor
  · rintro ⟨hidEndo, hleast⟩
    constructor
    · exact (mixedEndomorphism_iff_functional_fixpoint F A
        (OrderedDomain.idContFun A.object)).1 hidEndo
    · intro h hh
      exact hleast h ((mixedEndomorphism_iff_functional_fixpoint F A h).2 hh)
  · rintro ⟨hidFix, hleast⟩
    constructor
    · exact (mixedEndomorphism_iff_functional_fixpoint F A
        (OrderedDomain.idContFun A.object)).2 hidFix
    · intro h hh
      exact hleast h ((mixedEndomorphism_iff_functional_fixpoint F A h).1 hh)

/-- The paired bilimit approximation equations make the identity the least
mixed endomorphism of a canonical mixed solution. -/
theorem canonicalIdentityIsLeastMixedEndomorphism
    (F : MixedVariantFunctor.{u}) (C : MixedCanonicalSolution F) :
    IdentityIsLeastMixedEndomorphism F C.solution := by
  letI : OrderBot C.construction.baseLeft.carrier :=
    C.construction.baseLeft_orderBot
  letI : OrderBot C.construction.baseRight.carrier :=
    C.construction.baseRight_orderBot
  letI : OrderBot C.solution.object.carrier := C.construction.solution_orderBot
  constructor
  · intro x
    change C.solution.fold x =
      C.solution.fold
        (F.mapHom (OrderedDomain.idContFun C.solution.object)
          (OrderedDomain.idContFun C.solution.object) x)
    rw [F.mapHom_id]
  · intro h hh
    apply C.construction.identity_is_sup_left_stage_approximations.2 h
    intro q hq
    rcases hq with ⟨n, rfl⟩
    have hstage : ∀ m : Nat,
        epApproximationContFun (C.construction.leftStagePair m) ≤ h ∧
          epApproximationContFun (C.construction.rightStagePair m) ≤ h := by
      intro m
      induction m with
      | zero =>
          constructor
          · intro x
            calc
              epApproximationContFun (C.construction.leftStagePair 0) x =
                  (C.construction.leftStagePair 0).e
                    ((C.construction.leftStagePair 0).p x) := rfl
              _ = (C.construction.leftStagePair 0).e
                  (⊥ : C.construction.baseLeft.carrier) := by
                    congr 1
                    exact C.construction.baseLeft_subsingleton _ _
              _ = ⊥ := C.construction.left_stage_zero_strict
              _ ≤ h x := bot_le
          · intro x
            calc
              epApproximationContFun (C.construction.rightStagePair 0) x =
                  (C.construction.rightStagePair 0).e
                    ((C.construction.rightStagePair 0).p x) := rfl
              _ = (C.construction.rightStagePair 0).e
                  (⊥ : C.construction.baseRight.carrier) := by
                    congr 1
                    exact C.construction.baseRight_subsingleton _ _
              _ = ⊥ := C.construction.right_stage_zero_strict
              _ ≤ h x := bot_le
      | succ m ih =>
          have hmono := Chapter3.ScottContinuous.monotone
            (C.construction.locallyContinuous.hom_continuous
              (D₁ := C.solution.object) (D₂ := C.solution.object)
              (E₁ := C.solution.object) (E₂ := C.solution.object))
          constructor
          · intro x
            have hp :
                (C.construction.leftStagePair (m + 1)).p x =
                  F.mapHom
                    (epEmbeddingContFun (C.construction.rightStagePair m))
                    (epProjectionContFun (C.construction.leftStagePair m))
                    (C.solution.unfold x) := by
              calc
                (C.construction.leftStagePair (m + 1)).p x =
                    (C.construction.leftStagePair (m + 1)).p
                      (C.solution.fold (C.solution.unfold x)) := by
                        rw [C.solution.fold_unfold]
                _ = _ := C.construction.left_fold_stage_projection m
                  (C.solution.unfold x)
            have he : ∀ y :
                (MixedFunctorLeftObject F C.construction.baseLeft
                  C.construction.baseRight (m + 1)).carrier,
                (C.construction.leftStagePair (m + 1)).e y =
                  C.solution.fold
                    (F.mapHom
                      (epProjectionContFun (C.construction.rightStagePair m))
                      (epEmbeddingContFun (C.construction.leftStagePair m)) y) := by
              intro y
              calc
                (C.construction.leftStagePair (m + 1)).e y =
                    C.solution.fold
                      (C.solution.unfold
                        ((C.construction.leftStagePair (m + 1)).e y)) :=
                  (C.solution.fold_unfold _).symm
                _ = _ := by rw [C.construction.left_unfold_stage_embedding]
            calc
              epApproximationContFun (C.construction.leftStagePair (m + 1)) x =
                  (C.construction.leftStagePair (m + 1)).e
                    ((C.construction.leftStagePair (m + 1)).p x) := rfl
              _ = C.solution.fold
                  (F.mapHom
                    (epProjectionContFun (C.construction.rightStagePair m))
                    (epEmbeddingContFun (C.construction.leftStagePair m))
                    ((C.construction.leftStagePair (m + 1)).p x)) := he _
              _ = C.solution.fold
                  (F.mapHom
                    (epProjectionContFun (C.construction.rightStagePair m))
                    (epEmbeddingContFun (C.construction.leftStagePair m))
                    (F.mapHom
                      (epEmbeddingContFun (C.construction.rightStagePair m))
                      (epProjectionContFun (C.construction.leftStagePair m))
                      (C.solution.unfold x))) := by rw [hp]
              _ = C.solution.fold
                  (F.mapHom
                    (OrderedDomain.compContFun
                      (epEmbeddingContFun (C.construction.rightStagePair m))
                      (epProjectionContFun (C.construction.rightStagePair m)))
                    (OrderedDomain.compContFun
                      (epEmbeddingContFun (C.construction.leftStagePair m))
                      (epProjectionContFun (C.construction.leftStagePair m)))
                    (C.solution.unfold x)) := by
                      rw [F.mapHom_comp]
              _ = C.solution.fold
                  (F.mapHom
                    (epApproximationContFun (C.construction.rightStagePair m))
                    (epApproximationContFun (C.construction.leftStagePair m))
                    (C.solution.unfold x)) := rfl
              _ ≤ h x := by
                have hle :
                    C.solution.fold
                        (F.mapHom
                          (epApproximationContFun
                            (C.construction.rightStagePair m))
                          (epApproximationContFun
                            (C.construction.leftStagePair m))
                          (C.solution.unfold x)) ≤
                      C.solution.fold (F.mapHom h h (C.solution.unfold x)) := by
                  have hpair :
                      (epApproximationContFun (C.construction.rightStagePair m),
                        epApproximationContFun (C.construction.leftStagePair m)) ≤
                      (h, h) := ⟨ih.2, ih.1⟩
                  exact C.solution.fold.continuous.1
                    (hmono hpair (C.solution.unfold x))
                have heq : C.solution.fold (F.mapHom h h (C.solution.unfold x)) =
                    h x := by
                  calc
                    C.solution.fold (F.mapHom h h (C.solution.unfold x)) =
                        h (C.solution.fold (C.solution.unfold x)) :=
                      (hh (C.solution.unfold x)).symm
                    _ = h x := by rw [C.solution.fold_unfold]
                exact le_trans hle (le_of_eq heq)
          · intro x
            have hp :
                (C.construction.rightStagePair (m + 1)).p x =
                  F.mapHom
                    (epEmbeddingContFun (C.construction.leftStagePair m))
                    (epProjectionContFun (C.construction.rightStagePair m))
                    (C.solution.unfold x) := by
              calc
                (C.construction.rightStagePair (m + 1)).p x =
                    (C.construction.rightStagePair (m + 1)).p
                      (C.solution.fold (C.solution.unfold x)) := by
                        rw [C.solution.fold_unfold]
                _ = _ := C.construction.right_fold_stage_projection m
                  (C.solution.unfold x)
            have he : ∀ y :
                (MixedFunctorRightObject F C.construction.baseLeft
                  C.construction.baseRight (m + 1)).carrier,
                (C.construction.rightStagePair (m + 1)).e y =
                  C.solution.fold
                    (F.mapHom
                      (epProjectionContFun (C.construction.leftStagePair m))
                      (epEmbeddingContFun (C.construction.rightStagePair m)) y) := by
              intro y
              calc
                (C.construction.rightStagePair (m + 1)).e y =
                    C.solution.fold
                      (C.solution.unfold
                        ((C.construction.rightStagePair (m + 1)).e y)) :=
                  (C.solution.fold_unfold _).symm
                _ = _ := by rw [C.construction.right_unfold_stage_embedding]
            calc
              epApproximationContFun (C.construction.rightStagePair (m + 1)) x =
                  (C.construction.rightStagePair (m + 1)).e
                    ((C.construction.rightStagePair (m + 1)).p x) := rfl
              _ = C.solution.fold
                  (F.mapHom
                    (epProjectionContFun (C.construction.leftStagePair m))
                    (epEmbeddingContFun (C.construction.rightStagePair m))
                    ((C.construction.rightStagePair (m + 1)).p x)) := he _
              _ = C.solution.fold
                  (F.mapHom
                    (epProjectionContFun (C.construction.leftStagePair m))
                    (epEmbeddingContFun (C.construction.rightStagePair m))
                    (F.mapHom
                      (epEmbeddingContFun (C.construction.leftStagePair m))
                      (epProjectionContFun (C.construction.rightStagePair m))
                      (C.solution.unfold x))) := by rw [hp]
              _ = C.solution.fold
                  (F.mapHom
                    (OrderedDomain.compContFun
                      (epEmbeddingContFun (C.construction.leftStagePair m))
                      (epProjectionContFun (C.construction.leftStagePair m)))
                    (OrderedDomain.compContFun
                      (epEmbeddingContFun (C.construction.rightStagePair m))
                      (epProjectionContFun (C.construction.rightStagePair m)))
                    (C.solution.unfold x)) := by
                      rw [F.mapHom_comp]
              _ = C.solution.fold
                  (F.mapHom
                    (epApproximationContFun (C.construction.leftStagePair m))
                    (epApproximationContFun (C.construction.rightStagePair m))
                    (C.solution.unfold x)) := rfl
              _ ≤ h x := by
                have hle :
                    C.solution.fold
                        (F.mapHom
                          (epApproximationContFun
                            (C.construction.leftStagePair m))
                          (epApproximationContFun
                            (C.construction.rightStagePair m))
                          (C.solution.unfold x)) ≤
                      C.solution.fold (F.mapHom h h (C.solution.unfold x)) := by
                  have hpair :
                      (epApproximationContFun (C.construction.leftStagePair m),
                        epApproximationContFun (C.construction.rightStagePair m)) ≤
                      (h, h) := ⟨ih.1, ih.2⟩
                  exact C.solution.fold.continuous.1
                    (hmono hpair (C.solution.unfold x))
                have heq : C.solution.fold (F.mapHom h h (C.solution.unfold x)) =
                    h x := by
                  calc
                    C.solution.fold (F.mapHom h h (C.solution.unfold x)) =
                        h (C.solution.fold (C.solution.unfold x)) :=
                      (hh (C.solution.unfold x)).symm
                    _ = h x := by rw [C.solution.fold_unfold]
                exact le_trans hle (le_of_eq heq)
    exact (hstage n).1

/-- If the identity is the least diagonal fixed point, then the simultaneous
least mixed endomorphism pair consists of two identity maps. -/
theorem leastMixedEndomorphismMaps_eq_identity
    (F : MixedVariantFunctor.{u}) (hF : def_5_2_5_mixed_variant_functor F)
    (A : MixedDomainEquationSolution F)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hAanti : ∀ x y : A.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFAA : Chapter3.IsDcpo (F.mapObj A.object A.object).carrier)
    [OrderBot A.object.carrier]
    (hIdentity : IdentityIsLeastMixedFunctionalFixpoint F A) :
    (leastMixedHomMaps F hF A A hAdcpo hAdcpo hFAA hFAA).1 =
        OrderedDomain.idContFun A.object ∧
      (leastMixedHomMaps F hF A A hAdcpo hAdcpo hFAA hFAA).2 =
        OrderedDomain.idContFun A.object := by
  let l := leastMixedHomMaps F hF A A hAdcpo hAdcpo hFAA hFAA
  have hSpec := leastMixedHomMaps_spec F hF A A
    hAdcpo hAanti hAdcpo hAanti hFAA hFAA
  have hSwapFix : mixedHomFunctional F A A (l.2, l.1) = (l.2, l.1) := by
    have hFix := hSpec.1
    apply Prod.ext
    · exact congrArg Prod.snd hFix
    · exact congrArg Prod.fst hFix
  have hLeSwap : l ≤ (l.2, l.1) := hSpec.2 (l.2, l.1) hSwapFix
  have hComponents : l.1 = l.2 := by
    apply Chapter3.ContFun.ext_apply
    intro x
    exact hAanti _ _ (hLeSwap.1 x) (hLeSwap.2 x)
  have hDiagonalFix : mixedEndomorphismFunctional F A l.1 = l.1 := by
    have hFixFirst := congrArg Prod.fst hSpec.1
    change (mixedHomFunctional F A A l).1 = l.1 at hFixFirst
    change OrderedDomain.compContFun A.fold
      (OrderedDomain.compContFun (F.mapHom l.2 l.1) A.unfold) = l.1 at hFixFirst
    rw [← hComponents] at hFixFirst
    exact hFixFirst
  have hIdentityPairFix : mixedHomFunctional F A A
      (OrderedDomain.idContFun A.object, OrderedDomain.idContFun A.object) =
        (OrderedDomain.idContFun A.object, OrderedDomain.idContFun A.object) := by
    apply Prod.ext
    · apply Chapter3.ContFun.ext_apply
      intro x
      change A.fold
          (F.mapHom (OrderedDomain.idContFun A.object)
            (OrderedDomain.idContFun A.object) (A.unfold x)) = x
      rw [F.mapHom_id, A.fold_unfold]
    · apply Chapter3.ContFun.ext_apply
      intro x
      change A.fold
          (F.mapHom (OrderedDomain.idContFun A.object)
            (OrderedDomain.idContFun A.object) (A.unfold x)) = x
      rw [F.mapHom_id, A.fold_unfold]
  have hLeIdentity := hSpec.2
    (OrderedDomain.idContFun A.object, OrderedDomain.idContFun A.object)
    hIdentityPairFix
  have hIdentityLe := hIdentity.2 l.1 hDiagonalFix
  have hFirst : l.1 = OrderedDomain.idContFun A.object := by
    apply Chapter3.ContFun.ext_apply
    intro x
    exact hAanti _ _ (hLeIdentity.1 x) (hIdentityLe x)
  exact ⟨hFirst, Eq.trans hComponents.symm hFirst⟩

/-- Uniqueness of strict diagonal mixed endomorphisms forces the identity to be
the least diagonal fixed point. -/
theorem identityLeastMixedFunctionalFixpoint_of_identityOnlyStrict
    (F : MixedVariantFunctor.{u}) (hF : def_5_2_5_mixed_variant_functor F)
    (A : MixedDomainEquationSolution F)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hAanti : ∀ x y : A.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFAA : Chapter3.IsDcpo (F.mapObj A.object A.object).carrier)
    [OrderBot A.object.carrier]
    (hUnique : IdentityOnlyBottomStrictMixedEndomorphism F A) :
    IdentityIsLeastMixedFunctionalFixpoint F A := by
  let l := leastMixedHomMaps F hF A A hAdcpo hAdcpo hFAA hFAA
  have hSpec := leastMixedHomMaps_spec F hF A A
    hAdcpo hAanti hAdcpo hAanti hFAA hFAA
  have hSwapFix : mixedHomFunctional F A A (l.2, l.1) = (l.2, l.1) := by
    have hFix := hSpec.1
    apply Prod.ext
    · exact congrArg Prod.snd hFix
    · exact congrArg Prod.fst hFix
  have hLeSwap : l ≤ (l.2, l.1) := hSpec.2 (l.2, l.1) hSwapFix
  have hComponents : l.1 = l.2 := by
    apply Chapter3.ContFun.ext_apply
    intro x
    exact hAanti _ _ (hLeSwap.1 x) (hLeSwap.2 x)
  have hDiagonalFix : mixedEndomorphismFunctional F A l.1 = l.1 := by
    have hFixFirst := congrArg Prod.fst hSpec.1
    change (mixedHomFunctional F A A l).1 = l.1 at hFixFirst
    change OrderedDomain.compContFun A.fold
      (OrderedDomain.compContFun (F.mapHom l.2 l.1) A.unfold) = l.1 at hFixFirst
    rw [← hComponents] at hFixFirst
    exact hFixFirst
  have hIdentityPairFix : mixedHomFunctional F A A
      (OrderedDomain.idContFun A.object, OrderedDomain.idContFun A.object) =
        (OrderedDomain.idContFun A.object, OrderedDomain.idContFun A.object) := by
    apply Prod.ext
    · apply Chapter3.ContFun.ext_apply
      intro x
      change A.fold
          (F.mapHom (OrderedDomain.idContFun A.object)
            (OrderedDomain.idContFun A.object) (A.unfold x)) = x
      rw [F.mapHom_id, A.fold_unfold]
    · apply Chapter3.ContFun.ext_apply
      intro x
      change A.fold
          (F.mapHom (OrderedDomain.idContFun A.object)
            (OrderedDomain.idContFun A.object) (A.unfold x)) = x
      rw [F.mapHom_id, A.fold_unfold]
  have hLeIdentity := hSpec.2
    (OrderedDomain.idContFun A.object, OrderedDomain.idContFun A.object)
    hIdentityPairFix
  have hStrict : Chapter2.StrictMap l.1 :=
    hAanti _ _ (hLeIdentity.1 ⊥) bot_le
  have hEndomorphism : IsMixedEndomorphism F A l.1 :=
    (mixedEndomorphism_iff_functional_fixpoint F A l.1).2 hDiagonalFix
  have hFirst : l.1 = OrderedDomain.idContFun A.object :=
    hUnique l.1 hStrict hEndomorphism
  constructor
  · apply Chapter3.ContFun.ext_apply
    intro x
    change A.fold
        (F.mapHom (OrderedDomain.idContFun A.object)
          (OrderedDomain.idContFun A.object) (A.unfold x)) = x
    rw [F.mapHom_id, A.fold_unfold]
  · intro h hh
    have hPairFix : mixedHomFunctional F A A (h, h) = (h, h) := by
      apply Prod.ext <;> exact hh
    have hLeast := hSpec.2 (h, h) hPairFix
    change l ≤ (h, h) at hLeast
    have hFirstLe := hLeast.1
    rw [hFirst] at hFirstLe
    exact hFirstLe

/-- A diagonal least fixed point makes every strict mixed endomorphism equal to
the identity.  The proof uses simultaneous fixed-point invariance on the two
mixed hom coordinates. -/
theorem identityOnlyStrict_of_identityLeastMixedFunctionalFixpoint
    (F : MixedVariantFunctor.{u}) (hF : def_5_2_5_mixed_variant_functor F)
    (A : MixedDomainEquationSolution F)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hAanti : ∀ x y : A.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFAA : Chapter3.IsDcpo (F.mapObj A.object A.object).carrier)
    [OrderBot A.object.carrier]
    (hIdentity : IdentityIsLeastMixedFunctionalFixpoint F A) :
    IdentityOnlyBottomStrictMixedEndomorphism F A := by
  intro k hkStrict hkEndomorphism
  let phi := mixedHomFunctionalContFun F hF A A hFAA hFAA
  let postPre : Chapter3.ContFun (MixedHomMaps F A A) (MixedHomMaps F A A) :=
    { toFun := fun p =>
        (OrderedDomain.compContFun k p.1,
          OrderedDomain.compContFun p.2 k)
      continuous := Chapter3.prod_pair_scottContinuous
        (Chapter3.ScottContinuous.comp
          (postcompose_scottContinuous A.object A.object A.object hAdcpo k)
          Chapter3.prod_fst_scottContinuous)
        (Chapter3.ScottContinuous.comp
          (precompose_scottContinuous A.object A.object A.object hAdcpo k)
          Chapter3.prod_snd_scottContinuous) }
  have hPostPreStrict : postPre ⊥ = ⊥ := by
    apply Prod.ext
    · apply Chapter3.ContFun.ext_apply
      intro x
      exact hkStrict
    · apply Chapter3.ContFun.ext_apply
      intro x
      rfl
  have hkFix :=
    (mixedEndomorphism_iff_functional_fixpoint F A k).1 hkEndomorphism
  have hkPairFix : mixedHomFunctional F A A (k, k) = (k, k) := by
    apply Prod.ext <;> exact hkFix
  have hPostPreComm : ∀ p : MixedHomMaps F A A,
      postPre (phi p) = phi (postPre p) := by
    intro p
    calc
      postPre (phi p) = composeMixedHomMaps F A A A (phi p, (k, k)) := rfl
      _ = composeMixedHomMaps F A A A
          (mixedHomFunctional F A A p, mixedHomFunctional F A A (k, k)) := by
            change composeMixedHomMaps F A A A
              (mixedHomFunctional F A A p, (k, k)) = _
            rw [hkPairFix]
      _ = composeMixedHomMaps F A A A
          (mixedHomFunctionalProduct F A A A (p, (k, k))) := rfl
      _ = mixedHomFunctional F A A
          (composeMixedHomMaps F A A A (p, (k, k))) :=
            composeMixedHomMaps_functional F A A A (p, (k, k))
      _ = phi (postPre p) := rfl
  have hPairAnti := mixedHomMaps_antisymm F A A hAanti hAanti
  have hInvariant := preorderChosenLeastFix_invariance
    (D := MixedHomMaps F A A) (E := MixedHomMaps F A A)
    (Chapter3.prod_isDcpo
      (Chapter3.ContFun.isDcpo_of_codomain hAdcpo)
      (Chapter3.ContFun.isDcpo_of_codomain hAdcpo))
    (Chapter3.prod_isDcpo
      (Chapter3.ContFun.isDcpo_of_codomain hAdcpo)
      (Chapter3.ContFun.isDcpo_of_codomain hAdcpo))
    hPairAnti phi phi postPre hPostPreStrict hPostPreComm
  have hLeastIdentity := leastMixedEndomorphismMaps_eq_identity
    F hF A hAdcpo hAanti hFAA hIdentity
  let l := leastMixedHomMaps F hF A A hAdcpo hAdcpo hFAA hFAA
  have hLEq : l =
      (OrderedDomain.idContFun A.object, OrderedDomain.idContFun A.object) := by
    apply Prod.ext
    · exact hLeastIdentity.1
    · exact hLeastIdentity.2
  change l = postPre l at hInvariant
  rw [hLEq] at hInvariant
  apply Chapter3.ContFun.ext_apply
  intro x
  have hx := congrArg (fun p => p.1 x) hInvariant
  exact hx.symm

/-- Leastness of the identity mixed endomorphism is invariant under an
isomorphism of mixed recursive-equation solutions. -/
theorem identityLeastMixedEndomorphism_of_solutionIso
    (F : MixedVariantFunctor.{u})
    (A C : MixedDomainEquationSolution F)
    (i : MixedSolutionIso F A C)
    (hC : IdentityIsLeastMixedEndomorphism F C) :
    IdentityIsLeastMixedEndomorphism F A := by
  constructor
  · intro x
    change A.fold x = A.fold
      (F.mapHom (OrderedDomain.idContFun A.object)
        (OrderedDomain.idContFun A.object) x)
    rw [F.mapHom_id]
  · intro h hh
    let diagonal : MixedHomPair F A A :=
      { forward := h
        backward := h
        forward_commutes := hh
        backward_commutes := hh }
    let conjugate : MixedHomPair F C C :=
      MixedHomPair.comp i.homPair
        (MixedHomPair.comp diagonal (MixedHomPair.reverse i.homPair))
    have hConjugateEq : conjugate.backward = conjugate.forward := by
      apply Chapter3.ContFun.ext_apply
      intro x
      rfl
    have hConjugateEnd : IsMixedEndomorphism F C conjugate.forward := by
      intro x
      have hx := conjugate.forward_commutes x
      rw [hConjugateEq] at hx
      exact hx
    have hConjugateLeast := hC.2 conjugate.forward hConjugateEnd
    intro x
    calc
      x = i.homPair.backward (i.homPair.forward x) :=
        (i.backward_forward_id x).symm
      _ ≤ i.homPair.backward (conjugate.forward (i.homPair.forward x)) :=
        i.homPair.backward.continuous.1 (hConjugateLeast (i.homPair.forward x))
      _ = i.homPair.backward
          (i.homPair.forward
            (h (i.homPair.backward (i.homPair.forward x)))) := rfl
      _ = h (i.homPair.backward (i.homPair.forward x)) :=
        i.backward_forward_id _
      _ = h x := congrArg h (i.backward_forward_id x)

/-- A chosen canonical mixed solution is isomorphic to any solution whose
identity is the least diagonal fixed point. -/
theorem mixedSolutionIsoCanonical_of_identityLeast
    (F : MixedVariantFunctor.{u}) (hF : def_5_2_5_mixed_variant_functor F)
    (C : MixedCanonicalSolution F)
    (A : MixedDomainEquationSolution F)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hAanti : ∀ x y : A.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFAA : Chapter3.IsDcpo (F.mapObj A.object A.object).carrier)
    [OrderBot A.object.carrier]
    (hIdentity : IdentityIsLeastMixedFunctionalFixpoint F A) :
    Nonempty (MixedSolutionIso F A C.solution) := by
  letI cBot : OrderBot C.solution.object.carrier :=
    C.construction.solution_orderBot
  let p : MixedHomPair F A C.solution :=
    leastMixedHomPair F hF A C.solution
      hAdcpo hAanti C.construction.solution_dcpo
        C.construction.solution_antisymm hFAA
          C.construction.functor_solution_dcpo
  let q : MixedHomPair F C.solution A := MixedHomPair.reverse p
  have hp : IsLeastMixedHomPair F A C.solution p :=
    leastMixedHomPair_isLeast F hF A C.solution
      hAdcpo hAanti C.construction.solution_dcpo
        C.construction.solution_antisymm hFAA
          C.construction.functor_solution_dcpo
  have hq : IsLeastMixedHomPair F C.solution A q := by
    intro r
    have hr := hp (MixedHomPair.reverse r)
    exact ⟨hr.2, hr.1⟩
  let endA : MixedHomPair F A A := MixedHomPair.comp q p
  let endC : MixedHomPair F C.solution C.solution := MixedHomPair.comp p q
  have hEndA : IsLeastMixedHomPair F A A endA :=
    lemma_5_3_6_mixed_hom_pair_composition F hF A C.solution A
      hAdcpo hAanti C.construction.solution_dcpo
        C.construction.solution_antisymm hAdcpo hAanti hFAA
          C.construction.functor_solution_dcpo hFAA p q endA hp hq rfl rfl
  have hEndC : IsLeastMixedHomPair F C.solution C.solution endC :=
    lemma_5_3_6_mixed_hom_pair_composition F hF C.solution A C.solution
      C.construction.solution_dcpo C.construction.solution_antisymm
        hAdcpo hAanti C.construction.solution_dcpo
          C.construction.solution_antisymm
            C.construction.functor_solution_dcpo hFAA
              C.construction.functor_solution_dcpo q p endC hq hp rfl rfl
  let leastA := leastMixedHomPair F hF A A
    hAdcpo hAanti hAdcpo hAanti hFAA hFAA
  let leastC := leastMixedHomPair F hF C.solution C.solution
    C.construction.solution_dcpo C.construction.solution_antisymm
      C.construction.solution_dcpo C.construction.solution_antisymm
        C.construction.functor_solution_dcpo
          C.construction.functor_solution_dcpo
  have hLeastA := leastMixedHomPair_isLeast F hF A A
    hAdcpo hAanti hAdcpo hAanti hFAA hFAA
  have hLeastC := leastMixedHomPair_isLeast F hF C.solution C.solution
    C.construction.solution_dcpo C.construction.solution_antisymm
      C.construction.solution_dcpo C.construction.solution_antisymm
        C.construction.functor_solution_dcpo
          C.construction.functor_solution_dcpo
  have hAIdentityMaps := leastMixedEndomorphismMaps_eq_identity
    F hF A hAdcpo hAanti hFAA hIdentity
  have hCIdentity : IdentityIsLeastMixedFunctionalFixpoint F C.solution :=
    (identityLeastMixedEndomorphism_iff_identityLeastMixedFunctionalFixpoint
      F C.solution).1 (canonicalIdentityIsLeastMixedEndomorphism F C)
  have hCIdentityMaps := leastMixedEndomorphismMaps_eq_identity
    F hF C.solution C.construction.solution_dcpo
      C.construction.solution_antisymm C.construction.functor_solution_dcpo
        hCIdentity
  have hLeastAForward : leastA.forward = OrderedDomain.idContFun A.object := by
    exact hAIdentityMaps.1
  have hLeastCForward : leastC.forward =
      OrderedDomain.idContFun C.solution.object := by
    exact hCIdentityMaps.1
  have hEndAForward : endA.forward = OrderedDomain.idContFun A.object := by
    apply Chapter3.ContFun.ext_apply
    intro x
    have hToIdentity := (hEndA leastA).1 x
    have hFromIdentity := (hLeastA endA).1 x
    rw [hLeastAForward] at hToIdentity hFromIdentity
    exact hAanti _ _ hToIdentity hFromIdentity
  have hEndCForward : endC.forward =
      OrderedDomain.idContFun C.solution.object := by
    apply Chapter3.ContFun.ext_apply
    intro x
    have hToIdentity := (hEndC leastC).1 x
    have hFromIdentity := (hLeastC endC).1 x
    rw [hLeastCForward] at hToIdentity hFromIdentity
    exact C.construction.solution_antisymm _ _ hToIdentity hFromIdentity
  exact ⟨
    { homPair := p
      forward_backward_id := by
        intro x
        have hx := congrArg (fun f => f x) hEndCForward
        exact hx
      backward_forward_id := by
        intro x
        have hx := congrArg (fun f => f x) hEndAForward
        exact hx }⟩

/-- Theorem 5.3.7, invariance part 2.  PDF text: for a mixed-variant locally
continuous functor and an isomorphism `i : F(A,A) -> A`, canonicity,
least mixed endomorphism, least fixed point of `φ(g) = i ∘ F(g,g) ∘ i⁻¹`, and
uniqueness of strict mixed endomorphisms are equivalent.

All domain-completeness assumptions are explicit because the lightweight
`OrderedDomain` bundle stores only its preorder. -/
theorem theorem_5_3_7_invariance_part2
    (F : MixedVariantFunctor.{u}) (hF : def_5_2_5_mixed_variant_functor F)
    (C : MixedCanonicalSolution F)
    (A : MixedDomainEquationSolution F)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hAanti : ∀ x y : A.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFAA : Chapter3.IsDcpo (F.mapObj A.object A.object).carrier)
    [OrderBot A.object.carrier] :
    (IsCanonicalMixedFixpoint F A ↔ IdentityIsLeastMixedEndomorphism F A) ∧
      (IdentityIsLeastMixedEndomorphism F A ↔
        IdentityIsLeastMixedFunctionalFixpoint F A) ∧
      (IdentityIsLeastMixedFunctionalFixpoint F A ↔
        IdentityOnlyBottomStrictMixedEndomorphism F A) := by
  have h1to2 : IsCanonicalMixedFixpoint F A →
      IdentityIsLeastMixedEndomorphism F A := by
    rintro ⟨C', ⟨i⟩⟩
    exact identityLeastMixedEndomorphism_of_solutionIso F A C'.solution i
      (canonicalIdentityIsLeastMixedEndomorphism F C')
  have h2iff3 :=
    identityLeastMixedEndomorphism_iff_identityLeastMixedFunctionalFixpoint F A
  have h3to4 : IdentityIsLeastMixedFunctionalFixpoint F A →
      IdentityOnlyBottomStrictMixedEndomorphism F A := by
    exact identityOnlyStrict_of_identityLeastMixedFunctionalFixpoint
      F hF A hAdcpo hAanti hFAA
  have h4to3 : IdentityOnlyBottomStrictMixedEndomorphism F A →
      IdentityIsLeastMixedFunctionalFixpoint F A := by
    exact identityLeastMixedFunctionalFixpoint_of_identityOnlyStrict
      F hF A hAdcpo hAanti hFAA
  have h3to1 : IdentityIsLeastMixedFunctionalFixpoint F A →
      IsCanonicalMixedFixpoint F A := by
    intro h3
    exact ⟨C, mixedSolutionIsoCanonical_of_identityLeast
      F hF C A hAdcpo hAanti hFAA h3⟩
  refine ⟨?_, h2iff3, ?_⟩
  · constructor
    · exact h1to2
    · intro h2
      exact h3to1 (h2iff3.1 h2)
  · exact ⟨h3to4, h4to3⟩

/-- Compatibility name for the bottom-strict statement of Theorem 5.3.7. -/
theorem theorem_5_3_7_invariance_part2_bottom_strict
    (F : MixedVariantFunctor.{u}) (hF : def_5_2_5_mixed_variant_functor F)
    (C : MixedCanonicalSolution F)
    (A : MixedDomainEquationSolution F)
    (hAdcpo : Chapter3.IsDcpo A.object.carrier)
    (hAanti : ∀ x y : A.object.carrier, x ≤ y → y ≤ x → x = y)
    (hFAA : Chapter3.IsDcpo (F.mapObj A.object A.object).carrier)
    [OrderBot A.object.carrier] :
    (IsCanonicalMixedFixpoint F A ↔ IdentityIsLeastMixedEndomorphism F A) ∧
      (IdentityIsLeastMixedEndomorphism F A ↔
        IdentityIsLeastMixedFunctionalFixpoint F A) ∧
      (IdentityIsLeastMixedFunctionalFixpoint F A ↔
        IdentityOnlyBottomStrictMixedEndomorphism F A) := by
  exact theorem_5_3_7_invariance_part2 F hF C A hAdcpo hAanti hFAA

/-- Theorem 5.3.8.  PDF text: the canonical fixpoint of a mixed-variant locally
continuous functor is a sub-domain of every other fixpoint.

This remains local proof debt until it is derived from the paired
mixed-variance bilimit construction. -/
theorem theorem_5_3_8_minimality_part2
    (F : MixedVariantFunctor.{u}) (_hF : def_5_2_5_mixed_variant_functor F)
    (C : MixedCanonicalSolution F) (S : MixedDomainEquationSolution F) :
    Nonempty (SubdomainOf C.solution.object S.object) := by
  admit

/-- Theorem 5.3.9.  PDF text: for the canonical solution `D` of
`X ≅ F(X,X)`, every pair of strict continuous functions
`f : A -> F(B,A)` and `g : F(A,B) -> B` has unique strict functions
`h : A -> D` and `k : D -> B` making the two displayed diagrams commute.

This remains direct proof debt; the result must be derived from the canonical
mixed fixed-point construction. -/
theorem theorem_5_3_9_free_mixed_variant_algebra
    (F : MixedVariantFunctor.{u}) (hF : def_5_2_5_mixed_variant_functor F)
    (C : MixedCanonicalSolution F) (P : MixedFreeAlgebraProblem F)
    [OrderBot P.A.carrier] [OrderBot P.B.carrier] [OrderBot C.solution.object.carrier]
    [OrderBot (F.mapObj P.B P.A).carrier] [OrderBot (F.mapObj P.A P.B).carrier]
    (hP : MixedFreeAlgebraProblem.IsStrict P) :
    ∃ S : MixedFreeAlgebraSolution F C.solution P,
      MixedFreeAlgebraSolution.IsStrict S ∧
        IsUniqueMixedFreeAlgebraSolution F C.solution P S := by
  admit

end Chapter5
end AbramskyJung

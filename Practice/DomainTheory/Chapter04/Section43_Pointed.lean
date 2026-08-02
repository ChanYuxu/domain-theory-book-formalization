import Practice.DomainTheory.Chapter04.Section43_ForbiddenObstructions

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Chapter 4, Section 4.3

Maximal cartesian closed subcategories and finite amalgams.

The classification theorems in this file are currently registered as visible
proof debt with auxiliary classification packages. The finite-amalgam
definition includes the PDF's finite cover by pointed sub-dcpos and the
intersection-closure clause.
-/

universe u

namespace AbramskyJung
namespace Chapter4

/-- Lemma 4.3.1, PDF text: if `[D -> E]` is continuous and `E` is pointed,
then `D` is coherent or `E` is an L-domain.

Exercise 4.3.11(3), which the book explicitly omits, is the visible `admit`
boundary reducing a non-L-domain to Figure 12's `A` or Figure 11's `X`.
The function-space retract and corrected `X` contradiction are proved.  The
remaining transitive `sorry` is confined to the source-supplied `A` case, whose
ordinal successor and pointwise-supremum details are under-specified in the
printed proof. -/
theorem lemma_4_3_1_cartesian_closed_separation
    (D E : OrderedDomain.{u})
    (hD : IsContinuousDomainObject D)
    (hE : IsPointedContinuousDomain E)
    (hFun : HasContinuousFunctionSpace D E) :
    IsCoherentDomain D ∨ IsLDomainObject E := by
  by_contra hConclusion
  rw [not_or] at hConclusion
  have hNotCoherent : ¬ IsCoherentDomain D := hConclusion.1
  have hNotL : ¬ IsLDomain E := by
    intro hL
    exact hConclusion.2 ⟨hE.toContinuousDomainObject, hL⟩
  rcases exercise_4_3_11_3_non_l_forbidden_retract E hE hNotL with
    hA | hX
  · rcases hA with ⟨A, ⟨hADiagram⟩, ⟨sr⟩⟩
    have hAdcpo : Chapter3.IsDcpo A.carrier :=
      sr.toSectionRetractionPair.isDcpo_of_isDcpo hE.1
    have hFunRetract := continuousFunctionSpaceRetract
      (D := D.carrier) sr hAdcpo hE.1
    have hFunA : Chapter3.IsContinuousDomain
        (Chapter3.ContFun D.carrier A.carrier) :=
      Chapter3.theorem_3_1_4_retract_continuous_domain_basis hFunRetract hFun.2
    exact not_continuous_functionSpace_of_figure12
      D A hD hNotCoherent hADiagram hAdcpo hFunA
  · rcases hX with ⟨X, ⟨hXDiagram⟩, ⟨sr⟩⟩
    have hXdcpo : Chapter3.IsDcpo X.carrier :=
      sr.toSectionRetractionPair.isDcpo_of_isDcpo hE.1
    have hFunRetract := continuousFunctionSpaceRetract
      (D := D.carrier) sr hXdcpo hE.1
    have hFunX : Chapter3.IsContinuousDomain
        (Chapter3.ContFun D.carrier X.carrier) :=
      Chapter3.theorem_3_1_4_retract_continuous_domain_basis hFunRetract hFun.2
    exact not_continuous_functionSpace_of_figure11
      D X hD hNotCoherent hXDiagram hXdcpo hFunX

/-- External implication used in Lemma 4.3.2.  Jung [Jun90, Corollary 2.2.14]
states that if a pointed dcpo `D` and `[D -> D]` are continuous and
Lawson-compact, then `D` is an FS-domain.  This declaration keeps precisely
those hypotheses; coherence is converted to Lawson compactness separately by
Proposition 4.2.20.

Reference: A. Jung, *The classification of continuous domains*, LICS 1990,
Corollary 2.2.14 (p. 52 in the reprint). -/
axiom jun90_corollary_2_2_14_fs_of_lawson_compact_self
    (D : OrderedDomain.{u})
    (hD : IsPointedContinuousDomain D)
    (hFun : HasContinuousSelfFunctionSpace D)
    (hCompactD : IsLawsonCompact D)
    (hCompactFun : IsLawsonCompact (OrderedDomain.functionSpace D D)) :
    IsFSObject D

/-- Lemma 4.3.2, PDF text: a bottomed continuous domain is FS iff it and its
self-function space are coherent.  The reverse implication is Jung [Jun90,
Corollary 2.2.14] after Proposition 4.2.20 converts coherence to Lawson
compactness.  The forward implication uses FS closure (Jung [Jun90,
Theorem 2.2.6]) and Theorem 4.2.18. -/
theorem lemma_4_3_2_bottomed_continuous_fs
    (D : OrderedDomain.{u}) (hD : IsPointedContinuousDomain D) :
    IsFSObject D ↔ IsCoherentDomain D ∧
      HasContinuousSelfFunctionSpace D ∧
        IsCoherentDomain (OrderedDomain.functionSpace D D) := by
  constructor
  · intro hFS
    have hCoherentD : IsCoherentDomain D :=
      (theorem_4_2_18_fs_bifinite_coherent D).1 hFS
    have hFSFun : IsFSObject (OrderedDomain.functionSpace D D) :=
      jun90_theorem_2_2_6_fs_closure.2.1 hFS hFS
    have hFunContinuous : HasContinuousSelfFunctionSpace D :=
      ⟨Chapter3.ContFun.isDcpo_of_codomain hD.1,
        fsObject_isContinuousDomain hFSFun⟩
    have hCoherentFun : IsCoherentDomain (OrderedDomain.functionSpace D D) :=
      (theorem_4_2_18_fs_bifinite_coherent
        (OrderedDomain.functionSpace D D)).1 hFSFun
    exact ⟨hCoherentD, hFunContinuous, hCoherentFun⟩
  · rintro ⟨hCoherentD, hFunContinuous, hCoherentFun⟩
    have hCompactD : IsLawsonCompact D :=
      (prop_4_2_20_lawson_topology_properties D hD.1 hD.2.2).2.2.2.2 hCoherentD
    have hCompactFun : IsLawsonCompact (OrderedDomain.functionSpace D D) :=
      (prop_4_2_20_lawson_topology_properties
        (OrderedDomain.functionSpace D D) hFunContinuous.1 hFunContinuous.2).2.2.2.2
          hCoherentFun
    exact jun90_corollary_2_2_14_fs_of_lawson_compact_self
      D hD hFunContinuous hCompactD hCompactFun

/-- Theorem 4.3.3, PDF text: every cartesian closed full subcategory of
`CONT⊥` is contained in `FS` or `L`.  The proof uses the 4.3.1 separation lemma
and the externally cited 4.3.2 FS/coherence characterization. -/
theorem theorem_4_3_3_cartesian_closed_contbot_subset_fs (C : DomainClass.{u})
    (hC : DomainClass.CartesianClosedSubcategoryOf
      (PointedContinuousDomainClass : DomainClass.{u}) C) :
    DomainClass.Subclass C (FSDomainClass : DomainClass.{u}) ∨
      DomainClass.Subclass C (LDomainObjectClass : DomainClass.{u}) := by
  classical
  by_cases hAllL : ∀ D : OrderedDomain.{u}, C.Obj D → IsLDomainObject D
  · exact Or.inr hAllL
  · have hExistsNotL :
        ∃ E : OrderedDomain.{u}, C.Obj E ∧ ¬ IsLDomainObject E := by
      by_contra hnone
      apply hAllL
      intro D hD
      by_contra hDL
      exact hnone ⟨D, hD, hDL⟩
    rcases hExistsNotL with ⟨E, hEC, hEnotL⟩
    have hEpointed : IsPointedContinuousDomain E := hC.1 E hEC
    exact Or.inl (by
      intro D hDC
      have hDpointed : IsPointedContinuousDomain D := hC.1 D hDC
      have hDcont : IsContinuousDomainObject D :=
        hDpointed.toContinuousDomainObject
      have hFunDEC : C.Obj (OrderedDomain.functionSpace D E) :=
        hC.2.exponentials hDC hEC
      have hFunDEcont : HasContinuousFunctionSpace D E :=
        (hC.1 (OrderedDomain.functionSpace D E) hFunDEC).toContinuousDomainObject
      have hDcoherent : IsCoherentDomain D := by
        rcases lemma_4_3_1_cartesian_closed_separation D E hDcont hEpointed hFunDEcont with
          hcoh | hEL
        · exact hcoh
        · exact False.elim (hEnotL hEL)
      have hSelfC : C.Obj (OrderedDomain.functionSpace D D) :=
        hC.2.exponentials hDC hDC
      have hSelfCont : HasContinuousSelfFunctionSpace D :=
        (hC.1 (OrderedDomain.functionSpace D D) hSelfC).toContinuousDomainObject
      have hSelfFunC :
          C.Obj (OrderedDomain.functionSpace (OrderedDomain.functionSpace D D) E) :=
        hC.2.exponentials hSelfC hEC
      have hSelfFunCont : HasContinuousFunctionSpace (OrderedDomain.functionSpace D D) E :=
        (hC.1 (OrderedDomain.functionSpace (OrderedDomain.functionSpace D D) E)
          hSelfFunC).toContinuousDomainObject
      have hSelfCoherent : IsCoherentDomain (OrderedDomain.functionSpace D D) := by
        rcases lemma_4_3_1_cartesian_closed_separation
            (OrderedDomain.functionSpace D D) E hSelfCont hEpointed hSelfFunCont with
          hcoh | hEL
        · exact hcoh
        · exact False.elim (hEnotL hEL)
      exact (lemma_4_3_2_bottomed_continuous_fs D hDpointed).2
        ⟨hDcoherent, hSelfCont, hSelfCoherent⟩)

/-- Theorem 4.3.4, PDF text: every cartesian closed full subcategory of
`ALG⊥` is contained in `B` or `aL`.  The classification proof is registered as
local proof debt. -/
theorem theorem_4_3_4_cartesian_closed_algbot_subset_bifinite (C : DomainClass.{u})
    (hC : DomainClass.CartesianClosedSubcategoryOf
      (PointedAlgebraicDomainClass : DomainClass.{u}) C) :
    DomainClass.Subclass C (BifiniteDomainObjectClass : DomainClass.{u}) ∨
      DomainClass.Subclass C (AlgebraicLDomainObjectClass : DomainClass.{u}) := by
  classical
  by_cases hAllAlgL : ∀ D : OrderedDomain.{u}, C.Obj D → IsAlgebraicLDomainObject D
  · exact Or.inr hAllAlgL
  · have hExistsNotAlgL :
        ∃ E : OrderedDomain.{u}, C.Obj E ∧ ¬ IsAlgebraicLDomainObject E := by
      by_contra hnone
      apply hAllAlgL
      intro D hD
      by_contra hDL
      exact hnone ⟨D, hD, hDL⟩
    rcases hExistsNotAlgL with ⟨E, hEC, hEnotAlgL⟩
    have hEpointedAlg : IsPointedAlgebraicDomain E := hC.1 E hEC
    have hEpointed : IsPointedContinuousDomain E :=
      hEpointedAlg.toPointedContinuousDomain
    have hEnotL : ¬ IsLDomainObject E := by
      intro hEL
      exact hEnotAlgL
        ⟨hEpointedAlg.toAlgebraicDomainObject, hEL.2⟩
    exact Or.inl (by
      intro D hDC
      have hDpointedAlg : IsPointedAlgebraicDomain D := hC.1 D hDC
      have hDalgObj : IsAlgebraicDomainObject D :=
        hDpointedAlg.toAlgebraicDomainObject
      have hDpointed : IsPointedContinuousDomain D :=
        hDpointedAlg.toPointedContinuousDomain
      have hDcont : IsContinuousDomainObject D :=
        hDalgObj.toContinuousDomainObject
      have hFunDEC : C.Obj (OrderedDomain.functionSpace D E) :=
        hC.2.exponentials hDC hEC
      have hFunDEcont : HasContinuousFunctionSpace D E :=
        (hC.1 (OrderedDomain.functionSpace D E) hFunDEC).toAlgebraicDomainObject
          |>.toContinuousDomainObject
      have hDcoherent : IsCoherentDomain D := by
        rcases lemma_4_3_1_cartesian_closed_separation D E hDcont hEpointed hFunDEcont with
          hcoh | hEL
        · exact hcoh
        · exact False.elim (hEnotL hEL)
      have hSelfC : C.Obj (OrderedDomain.functionSpace D D) :=
        hC.2.exponentials hDC hDC
      have hSelfAlgObj : IsAlgebraicDomainObject (OrderedDomain.functionSpace D D) :=
        (hC.1 (OrderedDomain.functionSpace D D) hSelfC).toAlgebraicDomainObject
      have hSelfCont : HasContinuousSelfFunctionSpace D :=
        hSelfAlgObj.toContinuousDomainObject
      have hSelfFunC :
          C.Obj (OrderedDomain.functionSpace (OrderedDomain.functionSpace D D) E) :=
        hC.2.exponentials hSelfC hEC
      have hSelfFunCont : HasContinuousFunctionSpace (OrderedDomain.functionSpace D D) E :=
        (hC.1 (OrderedDomain.functionSpace (OrderedDomain.functionSpace D D) E)
          hSelfFunC).toAlgebraicDomainObject.toContinuousDomainObject
      have hSelfCoherent : IsCoherentDomain (OrderedDomain.functionSpace D D) := by
        rcases lemma_4_3_1_cartesian_closed_separation
            (OrderedDomain.functionSpace D D) E hSelfCont hEpointed hSelfFunCont with
          hcoh | hEL
        · exact hcoh
        · exact False.elim (hEnotL hEL)
      have hFS : IsFSObject D :=
        (lemma_4_3_2_bottomed_continuous_fs D hDpointed).2
          ⟨hDcoherent, hSelfCont, hSelfCoherent⟩
      exact ⟨hDalgObj, prop_4_2_12_algebraic_fs_bifinite D hDalgObj.2 hFS⟩)

/-- A countably based continuous-domain object, represented by a countable basis. -/
def HasCountableBasis (D : OrderedDomain.{u}) : Prop :=
  ∃ B : Set D.carrier, B.Countable ∧ Chapter3.IsBasis B

/-- Restrict a domain class to countably based objects. -/
def OmegaRestriction (C : DomainClass.{u}) : DomainClass.{u} where
  Obj := fun D => C.Obj D ∧ HasCountableBasis D

/-- Theorem 4.3.5, omega-continuous case.  The classification proof is
registered as local proof debt rather than as a principle projection. -/
theorem theorem_4_3_5_omega_continuous_cartesian_closed_subcategories
    (C : DomainClass.{u})
    (hCont : DomainClass.CartesianClosedSubcategoryOf
      (OmegaRestriction (PointedContinuousDomainClass : DomainClass.{u})) C) :
    DomainClass.Subclass C (OmegaRestriction (FSDomainClass : DomainClass.{u})) := by
  admit

/-- Theorem 4.3.5, omega-algebraic case.  The classification proof is
registered as local proof debt rather than as a principle projection. -/
theorem theorem_4_3_5_omega_algebraic_cartesian_closed_subcategories
    (C : DomainClass.{u})
    (hAlg : DomainClass.CartesianClosedSubcategoryOf
      (OmegaRestriction (PointedAlgebraicDomainClass : DomainClass.{u})) C) :
    DomainClass.Subclass C
      (OmegaRestriction (BifiniteDomainObjectClass : DomainClass.{u})) := by
  admit

/-- Theorem 4.3.5, PDF text: every cartesian closed full subcategory of
`ω-CONT⊥` (`ω-ALG⊥`) is contained in `ω-FS` (`ω-B`). -/
theorem theorem_4_3_5_omega_cartesian_closed_subcategories
    (Ccont Calg : DomainClass.{u})
    (hCont : DomainClass.CartesianClosedSubcategoryOf
      (OmegaRestriction (PointedContinuousDomainClass : DomainClass.{u})) Ccont)
    (hAlg : DomainClass.CartesianClosedSubcategoryOf
      (OmegaRestriction (PointedAlgebraicDomainClass : DomainClass.{u})) Calg) :
    DomainClass.Subclass Ccont (OmegaRestriction (FSDomainClass : DomainClass.{u})) ∧
      DomainClass.Subclass Calg
        (OmegaRestriction (BifiniteDomainObjectClass : DomainClass.{u})) := by
  exact ⟨theorem_4_3_5_omega_continuous_cartesian_closed_subcategories Ccont hCont,
    theorem_4_3_5_omega_algebraic_cartesian_closed_subcategories Calg hAlg⟩

end Chapter4
end AbramskyJung

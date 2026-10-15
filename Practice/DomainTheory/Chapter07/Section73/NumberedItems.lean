import Practice.DomainTheory.Chapter07.Section73.Semantics

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 7.3: numbered statements

This module follows one coherent dependency cluster inside the textbook
section. The stable public import remains
`Practice.DomainTheory.Chapter07.Section73`.
-/

universe u v

namespace AbramskyJung
namespace Chapter7

/-- Proposition 7.3.3 PDF-facing statement.

The PDF proves both directions using the spectrum functor and the unit
`A -> KΩ(spec(A))`.  The current `LocalicDescription` interface still lacks
that unit construction and its surjectivity theorem, so the source proof cannot
yet be assembled from earlier declarations. -/
theorem prop_7_3_3_localic_description_spectrum
    (A : DomainPrelocale.{u}) (D : Chapter4.BifiniteDomain.{u}) :
    Nonempty (LocalicDescription A D) ↔ Nonempty (SpecDomainIso A D) := by
  sorry

/-- Concrete data for the duality between domain prelocales and bifinite
domains.  Besides the high-level dual-equivalence package, it records that each
translation is witnessed by a localic description and the corresponding spectrum
isomorphism. -/
structure DomainPrelocaleDuality : Type (u + 1) where
  duality : DualEquivalenceData DomainPrelocale.{u} Chapter4.BifiniteDomain.{u}
  prelocale_to_domain_description :
    ∀ A : DomainPrelocale.{u}, Nonempty (LocalicDescription A (duality.left A))
  domain_to_prelocale_description :
    ∀ D : Chapter4.BifiniteDomain.{u}, Nonempty (LocalicDescription (duality.right D) D)
  prelocale_spectrum_iso :
    ∀ A : DomainPrelocale.{u}, Nonempty (SpecDomainIso A (duality.left A))
  domain_spectrum_iso :
    ∀ D : Chapter4.BifiniteDomain.{u}, Nonempty (SpecDomainIso (duality.right D) D)
  relation_to_scott_map :
    ∀ {A B : DomainPrelocale.{u}},
      JoinApproximablePrelocaleRelation A B →
        BifiniteScottContinuousMap (duality.left B) (duality.left A)
  scott_map_to_relation :
    ∀ {D E : Chapter4.BifiniteDomain.{u}},
      BifiniteScottContinuousMap D E →
        JoinApproximablePrelocaleRelation (duality.right E) (duality.right D)
  relation_scott_inverse_laws : Prop
  scott_relation_inverse_laws : Prop

/-- Theorem 7.3.4 PDF-facing statement.

The book calls this a slight extension of Theorem 7.2.30 but supplies no proof
of the categorical equivalence or the morphism correspondence. -/
theorem theorem_7_3_4_domain_prelocale_duality :
    Nonempty (DomainPrelocaleDuality.{u}) := by
  admit

/-- Proposition 7.3.6 PDF-facing statement.

The PDF gives the embedding/projection formulas and proves continuity,
well-definedness, and the two e-p laws.  Formalizing the prime-filter
well-definedness argument is the remaining source-proved boundary. -/
theorem prop_7_3_6_sub_prelocale_ep_pair
    (A B : DomainPrelocale.{u}) :
    (hAB : SubPrelocale A B) → Nonempty (SpectrumEmbeddingProjection A B hAB) := by
  sorry

/-- Corollary 7.3.7 PDF-facing statement.

The PDF constructs the embedding as `τB ∘ e' ∘ τA⁻¹`.  This depends on
Propositions 7.3.3 and 7.3.6 and remains source-proved transitive proof debt. -/
theorem cor_7_3_7_sub_prelocale_domain_embedding
    (A B : DomainPrelocale.{u}) (D E : Chapter4.BifiniteDomain.{u}) :
    (descA : LocalicDescription A D) →
      (descB : LocalicDescription B E) →
        (hAB : SubPrelocale A B) →
          Nonempty (SubPrelocaleDomainEmbedding A B D E descA descB hAB) := by
  sorry

/-- Lemma 7.3.8 PDF-facing statement.

The two PDF arguments use compactness of the subbasic domain set and finite
idempotent deflations of the bifinite source and target.  The latter deflation
interfaces are not yet exposed strongly enough for this topology equality. -/
theorem lemma_7_3_8_compact_open_scott_function_space
    (D E : Chapter4.BifiniteDomain.{u})
    (U : Set (Chapter4.OrderedDomain.ContFunCarrier D.object E.object)) :
    @Chapter2.ScottOpen
        (Chapter4.OrderedDomain.ContFunCarrier D.object E.object)
        (Chapter4.OrderedDomain.contFunPreorder D.object E.object) U ↔
      CompactOpenFunctionSpaceOpen D.object E.object U := by
  sorry

/-- Lemma 7.3.9 PDF-facing statement.

The PDF derives compactness from idempotent deflations `gₙ`, `g'ₘ` and the
induced function-space deflation.  Membership in the generated compact-open
topology is already proved by `functionSpacePredicate_compactOpenTopology`; the
Scott-open and compact fields still require the source construction. -/
theorem lemma_7_3_9_bifinite_function_space_compact_opens
    (D E : Chapter4.BifiniteDomain.{u})
    (A : CompactOpenSet D.object) (A' : CompactOpenSet E.object) :
    FunctionSpacePredicateCompactOpen D E A A' := by
  sorry

/-- Theorem 7.3.10 PDF-facing statement.

The preceding construction in the PDF supplies the generators, rules,
spectrum isomorphism, and naturality proof.  Those components remain to be
implemented as a concrete `FunctionSpacePrelocaleDescription`. -/
theorem theorem_7_3_10_function_space_prelocale
    (A B : DomainPrelocale.{u}) :
    Nonempty (FunctionSpacePrelocaleDescription A B) := by
  sorry

/-- Lemma 7.3.11 PDF-facing statement.

The PDF proves compact-openness by lifting an idempotent deflation and proves
the base claim from finite compact lenses.  Both arguments are represented in
the package fields but the lifted Plotkin deflation theorem is not yet present. -/
theorem lemma_7_3_11_plotkin_powerdomain_compact_opens
    (D : Chapter4.BifiniteDomain.{u})
    (O : CompactOpenSet D.object) :
    Nonempty (PlotkinModalCompactOpenPackage D O) := by
  sorry

/-- Theorem 7.3.13 PDF-facing representation statement.

The PDF constructs the Plotkin powerlocale and verifies definability and
naturality after Lemma 7.3.11.  The term-prelocale quotient and its spectrum
isomorphism have not yet been implemented. -/
theorem theorem_7_3_13_plotkin_powerlocale_representation :
    Nonempty (PlotkinPowerlocaleRepresentationData.{u}) := by
  sorry

/-- The object-level consequence of Theorem 7.3.13 for a fixed prelocale. -/
theorem theorem_7_3_13_plotkin_powerlocale_description
    (A : DomainPrelocale.{u}) :
    Nonempty (PlotkinPowerlocaleDescription A) := by
  rcases theorem_7_3_13_plotkin_powerlocale_representation with ⟨data⟩
  exact ⟨data.description A⟩

/-- Theorem 7.3.14 PDF-facing statement.

The PDF gives the directed-union construction, the interpretation map into the
bilimit, and the naturality calculation.  Encoding the coherent stage maps and
their compact-element factorization is the remaining source-proved boundary. -/
theorem theorem_7_3_14_prelocale_chains_bilimits
    (C : PrelocaleChain.{u}) :
    Nonempty (PrelocaleChainBilimitDescription C) := by
  sorry

/-- Theorem 7.3.15 PDF-facing statement.

The PDF derives this compositionally from the function-space, Plotkin, and
bilimit constructions (and the analogous elementary type constructors).  The
current package records every semantic clause, but constructing it remains
source-proved proof debt. -/
theorem theorem_7_3_15_interpretation_preserves_localic_descriptions
    {Var : Type u} (ρ : TypeInterpretationData Var)
    (hEnv : ∀ X : Var,
      Nonempty (LocalicDescription (ρ.localicEnv X) (ρ.domainEnv X))) :
    ∀ σ : TypeExpr Var,
      Nonempty (LocalicDescription
        (ρ.localicInterpretation σ) (ρ.domainInterpretation σ)) := by
  sorry

/-- Theorem 7.3.16 PDF-facing statement.

The book identifies this as a special case of Theorem 7.3.15.  The present
interface additionally and correctly requires the chosen localic interpretation
to equal the syntactic prelocale `L(σ)`; that identification is not exposed by
`TypeInterpretationAgreement`, so the specialization cannot yet be assembled. -/
theorem theorem_7_3_16_closed_type_expression_spectrum_sourceExact
    {Var : Type u} (σ : TypeExpr Var) (hσ : TypeExpr.IsClosed σ) :
    Nonempty (ClosedTypeSpectrumDescriptionFor σ hσ) := by
  sorry

/-- Compatibility theorem for the legacy `TypeExpr Empty` fragment.  The
source-facing declaration above also supports named recursive binders. -/
theorem theorem_7_3_16_closed_type_expression_spectrum
    (σ : ClosedTypeExpr) :
    Nonempty (ClosedTypeSpectrumDescription.{u} σ) := by
  sorry

/-- A decision procedure for the property language following the proof outline:
normalise expressions into finite disjunctions of explicit join-primes, decide
the preorder on primes, and lift the decision to arbitrary expressions. -/
structure PropertyLanguageDecisionProcedure (Var : Type u) where
  Prime : TypeExpr Var → Type u
  prime_expr : ∀ σ : TypeExpr Var, Prime σ → PropertyExpr Var σ
  prime_preorder : ∀ σ : TypeExpr Var, Prime σ → Prime σ → Prop
  prime_preorder_decidable :
    ∀ σ : TypeExpr Var, ∀ p q : Prime σ, Decidable (prime_preorder σ p q)
  finite_positive_rule_scheme : Prop
  monotone_inductive_definition : Prop
  expression_preorder_refl :
    ∀ σ : TypeExpr Var, ∀ φ : PropertyExpr Var σ,
      PropertyFormulaPreorder Var φ φ
  expression_preorder_trans :
    ∀ σ : TypeExpr Var, ∀ φ ψ χ : PropertyExpr Var σ,
      PropertyFormulaPreorder Var φ ψ →
        PropertyFormulaPreorder Var ψ χ →
          PropertyFormulaPreorder Var φ χ
  C_predicate : ∀ σ : TypeExpr Var, PropertyExpr Var σ → Prop
  T_predicate : ∀ σ : TypeExpr Var, PropertyExpr Var σ → Prop
  expression_has_finite_construction :
    ∀ σ : TypeExpr Var, ∀ φ : PropertyExpr Var σ, 0 < PropertyExpr.size φ
  prime_is_C :
    ∀ σ : TypeExpr Var, ∀ p : Prime σ, C_predicate σ (prime_expr σ p)
  C_predicate_complete :
    ∀ σ : TypeExpr Var, ∀ φ : PropertyExpr Var σ,
      C_predicate σ φ →
        ∃ p : Prime σ,
          PropertyFormulaPreorder Var φ (prime_expr σ p) ∧
            PropertyFormulaPreorder Var (prime_expr σ p) φ
  normalForm : ∀ σ : TypeExpr Var, PropertyExpr Var σ → List (Prime σ)
  normalForm_sound_complete :
    ∀ σ : TypeExpr Var, ∀ φ : PropertyExpr Var σ,
      let nf := PropertyExpr.finiteDisj ((normalForm σ φ).map (prime_expr σ))
      PropertyFormulaPreorder Var φ nf ∧ PropertyFormulaPreorder Var nf φ
  expression_preorder_decidable :
    ∀ σ : TypeExpr Var, ∀ φ ψ : PropertyExpr Var σ,
      Decidable (PropertyFormulaPreorder Var φ ψ)
  one_preorder_decidable :
    ∀ φ ψ : PropertyExpr Var .one,
      Decidable (PropertyFormulaPreorder Var φ ψ)
  prime_preorder_structural_reduction :
    ∀ σ : TypeExpr Var, ∀ p q : Prime σ,
      ∃ baseProblems : List (PropertyExpr Var .one × PropertyExpr Var .one),
        prime_preorder σ p q ↔
          ∀ problem : PropertyExpr Var .one × PropertyExpr Var .one,
            problem ∈ baseProblems →
              PropertyFormulaPreorder Var problem.1 problem.2
  prime_preorder_sound_complete :
    ∀ σ : TypeExpr Var, ∀ p q : Prime σ,
      PropertyFormulaPreorder Var (prime_expr σ p) (prime_expr σ q) ↔
        prime_preorder σ p q

/-- Decision data for the actual syntactic property preorder. -/
def PropertyLanguageDecisionData (Var : Type u) : Type u :=
  ∀ σ : TypeExpr Var, ∀ φ ψ : PropertyExpr Var σ,
    Decidable (PropertyFormulaPreorder Var φ ψ)

/-- The property language is decidable for the actual syntactic preorder. -/
def PropertyLanguageDecidable (Var : Type u) : Prop :=
  Nonempty (PropertyLanguageDecisionData Var)

/-- A concrete normal-form implementation witnessing the decidability result. -/
def HasPropertyLanguageDecisionProcedure (Var : Type u) : Prop :=
  Nonempty (PropertyLanguageDecisionProcedure Var)

/-- Theorem 7.3.17 PDF-facing statement.

The PDF supplies the normal-form and structural-reduction decision procedure.
The package below states each algorithmic obligation, but the mutually
recursive prime normalizer and its proofs have not yet been implemented. -/
theorem theorem_7_3_17_property_language_decidable
    (Var : Type u) :
    PropertyLanguageDecidable Var := by
  sorry

/-- Theorem 7.3.18 PDF-facing statement.

The book states soundness and completeness after displaying the calculus and
semantics, but does not provide a proof in this chapter. -/
theorem theorem_7_3_18_domain_logic_sound_complete
    {Var : Type u} (I : DomainLogicInterpretation Var) :
    DomainLogicSoundComplete I := by
  admit


end Chapter7
end AbramskyJung

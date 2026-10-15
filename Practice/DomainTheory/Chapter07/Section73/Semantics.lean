import Practice.DomainTheory.Chapter07.Section73.Calculus

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 7.3: unit model and interpretation agreement

This module follows one coherent dependency cluster inside the textbook
section. The stable public import remains
`Practice.DomainTheory.Chapter07.Section73`.
-/

universe u v

namespace AbramskyJung
namespace Chapter7

private theorem punit_scottOpen (U : Set PUnit) :
    @Chapter2.ScottOpen PUnit inferInstance U := by
  constructor
  · intro x y hy _hxy
    cases x
    cases y
    exact hy
  · intro A s hA hsub _hs
    cases s
    rcases hA.1 with ⟨a, ha⟩
    cases a
    exact hsub ha

private theorem punit_scottContinuous_const {D : Type u} [Preorder D] :
    @Chapter3.ScottContinuous D PUnit inferInstance inferInstance (fun _ => PUnit.unit) := by
  constructor
  · intro x y _hxy
    exact le_rfl
  · intro A s _hA _hs
    constructor
    · intro y hy
      rcases hy with ⟨a, _ha, rfl⟩
      exact le_rfl
    · intro y _hy
      cases y
      exact le_rfl

private def punitOrderedDomain : Chapter4.OrderedDomain.{u} where
  carrier := PUnit
  preorder := inferInstance

private def punitFiniteProjection : Chapter4.FiniteProjection punitOrderedDomain.{u} where
  toFun := fun x => x
  continuous := Chapter3.scottContinuous_id
  idem := by
    intro x
    rfl
  below := by
    intro x
    exact le_rfl
  finite_range := by
    exact (Set.finite_singleton PUnit.unit).subset (by
      intro x _hx
      cases x
      simp)

private def punitBifiniteDomain : Chapter4.BifiniteDomain.{u} where
  object := punitOrderedDomain
  projection := fun _ => punitFiniteProjection
  increasing := by
    intro n x
    exact le_rfl
  approximates := by
    intro x
    constructor
    · intro y _hy
      cases x
      cases y
      exact le_rfl
    · intro y _hy
      cases x
      cases y
      exact le_rfl

private theorem punit_univ_joinPrime :
    IsJoinPrimeRel
      (fun x y : Set PUnit => x ⊆ y) (fun x y => x ∪ y) ∅ Set.univ := by
  constructor
  · intro hzero
    exact hzero.1 (show PUnit.unit ∈ (Set.univ : Set PUnit) from trivial)
  · intro b c habc
    have hbc : PUnit.unit ∈ b ∪ c := habc trivial
    rcases hbc with hb | hc
    · left
      intro x _hx
      cases x
      exact hb
    · right
      intro x _hx
      cases x
      exact hc

private theorem punit_open_joinPrime_iff (a : Set PUnit) :
    a = Set.univ ↔
      IsJoinPrimeRel
        (fun x y : Set PUnit => x ⊆ y) (fun x y => x ∪ y) ∅ a := by
  constructor
  · intro ha
    simpa [ha] using punit_univ_joinPrime
  · intro hprime
    by_cases hunit : PUnit.unit ∈ a
    · ext x
      cases x
      constructor
      · intro _hx
        trivial
      · intro _hx
        exact hunit
    · have haEmpty : a = ∅ := by
        ext x
        cases x
        constructor
        · intro hx
          exact False.elim (hunit hx)
        · intro hx
          cases hx
      exact False.elim (hprime.1 ⟨by simp [haEmpty], by simp [haEmpty]⟩)

private def punitOpenPrelocale : DomainPrelocale.{u} where
  carrier := Set PUnit
  le := fun U V => U ⊆ V
  le_refl := by
    intro U x hx
    exact hx
  le_trans := by
    intro U V W hUV hVW x hx
    exact hVW (hUV hx)
  sup := fun U V => U ∪ V
  inf := fun U V => U ∩ V
  zero := ∅
  one := Set.univ
  C := fun U => U = Set.univ
  sup_is_sup := by
    intro a b c
    exact Set.union_subset_iff
  inf_is_inf := by
    intro a b c
    exact Set.subset_inter_iff
  zero_le := by
    intro a x hx
    cases hx
  le_one := by
    intro a x _hx
    trivial
  C_iff_join_prime := by
    intro a
    exact punit_open_joinPrime_iff a
  finite_prime_generation := by
    intro a
    by_cases hunit : PUnit.unit ∈ a
    · have ha : a = Set.univ := by
        ext x
        cases x
        constructor
        · intro _hx
          trivial
        · intro _hx
          exact hunit
      refine ⟨[Set.univ], ?_, ?_⟩
      · intro x hx
        simpa using hx
      · constructor <;> intro x hx
        · simpa [ListJoin, ha] using hx
        · simpa [ListJoin, ha] using hx
    · have ha : a = ∅ := by
        ext x
        cases x
        constructor
        · intro hx
          exact False.elim (hunit hx)
        · intro hx
          cases hx
      refine ⟨[], ?_, ?_⟩
      · intro x hx
        cases hx
      · constructor <;> intro x hx
        · simpa [ListJoin, ha] using hx
        · simpa [ListJoin, ha] using hx
  finite_mub_closure := by
    intro U _hUfin hUC
    let onlyTop : Set (Set PUnit) := {Set.univ}
    refine ⟨onlyTop, ?_, ?_, ?_, ?_⟩
    · simp [onlyTop]
    · intro S hS
      simpa [onlyTop, hUC S hS]
    · intro S hS
      simpa [onlyTop] using hS
    · intro W hWV
      refine ⟨onlyTop, (by intro z hz; simpa [onlyTop] using hz), ?_⟩
      refine ⟨Set.univ, Set.univ, ?_, ?_, ?_⟩
      · constructor
        · intro w hw
          have hwEq : w = Set.univ := by
            simpa [onlyTop] using hWV hw
          intro x _hx
          simpa [hwEq]
        · intro y _hy x _hx
          trivial
      · constructor
        · intro z hz
          have hzEq : z = Set.univ := by
            simpa [onlyTop] using hz
          intro x hx
          simpa [hzEq] using hx
        · intro y hy
          have huniv_mem : (Set.univ : Set PUnit) ∈ onlyTop := by
            simp [onlyTop]
          exact hy Set.univ huniv_mem
      · constructor <;> intro x hx <;> exact hx
  top_prime := rfl

private theorem punit_scottCompact (K : Set PUnit) :
    ScottCompactSet punitOrderedDomain.{u} K := by
  intro cover _hcover hsub
  by_cases hK : ∃ x : PUnit, x ∈ K
  · rcases hK with ⟨x, hx⟩
    cases x
    have hUnion : PUnit.unit ∈ ⋃₀ cover := hsub hx
    rcases hUnion with ⟨U, hUcover, hUunit⟩
    refine ⟨{U}, Set.finite_singleton U, ?_, ?_⟩
    · intro V hV
      simpa using hV ▸ hUcover
    · intro y _hy
      cases y
      exact ⟨U, by simp, hUunit⟩
  · refine ⟨∅, Set.finite_empty, ?_, ?_⟩
    · intro U hU
      cases hU
    · intro x hx
      exact False.elim (hK ⟨x, hx⟩)

private theorem punit_compact_unit :
    @Chapter2.Compact PUnit inferInstance PUnit.unit := by
  intro A _s hA _hs _hle
  rcases hA.1 with ⟨a, haA⟩
  refine ⟨a, haA, ?_⟩
  cases a
  exact le_rfl

private def punitLocalicDescription :
    LocalicDescription punitOpenPrelocale.{u} punitBifiniteDomain.{u} where
  interpret := fun U =>
    { carrier := U
      scott_open := punit_scottOpen U
      compact := punit_scottCompact U }
  surjective := by
    intro O
    exact ⟨O.carrier, rfl⟩
  order_preserving := by
    intro a b hab
    exact hab
  order_reflecting := by
    intro a b hab
    exact hab
  sup_preserving := by
    intro a b
    rfl
  inf_preserving := by
    intro a b
    rfl
  zero_preserving := rfl
  one_preserving := rfl
  C_to_principal := by
    intro a ha
    refine ⟨PUnit.unit, punit_compact_unit, ?_⟩
    ext x
    cases x
    constructor
    · intro _hx
      trivial
    · intro _hx
      rw [ha]
      trivial
  principal_surjective := by
    intro O hO
    rcases hO with ⟨c, _hc, hcarrier⟩
    refine ⟨Set.univ, rfl, ?_⟩
    have hOuniv : O.carrier = Set.univ := by
      rw [hcarrier]
      ext x
      cases x
      cases c
      simp
    rw [hOuniv]
    rfl

private theorem punit_set_empty_or_univ (U : Set PUnit) :
    U = ∅ ∨ U = Set.univ := by
  by_cases hunit : PUnit.unit ∈ U
  · right
    ext x
    cases x
    constructor
    · intro _hx
      trivial
    · intro _hx
      exact hunit
  · left
    ext x
    cases x
    constructor
    · intro hx
      exact False.elim (hunit hx)
    · intro hx
      cases hx

private theorem punit_set_univ_of_unit_mem {U : Set PUnit} (hunit : PUnit.unit ∈ U) :
    U = Set.univ := by
  ext x
  cases x
  constructor
  · intro _hx
    trivial
  · intro _hx
    exact hunit

/-- The unique proper prime filter of the unit prelocale. -/
private def punitTopSpec : Spec punitOpenPrelocale.{u} :=
  ⟨{U : Set PUnit | U = Set.univ}, by
    refine
      { one_mem := ?_
        zero_not_mem := ?_
        upward_closed := ?_
        inf_closed := ?_
        sup_prime := ?_ }
    · rfl
    · intro hEmpty
      change (∅ : Set PUnit) = Set.univ at hEmpty
      have hUnit : PUnit.unit ∈ (∅ : Set PUnit) := by
        rw [hEmpty]
        trivial
      exact hUnit
    · intro U V hU hUV
      change (U : Set PUnit) = Set.univ at hU
      change (V : Set PUnit) = Set.univ
      have hUVset : (show Set PUnit from U) ⊆ (show Set PUnit from V) := by
        simpa [punitOpenPrelocale] using hUV
      have hUunit : PUnit.unit ∈ (show Set PUnit from U) := by
        rw [hU]
        trivial
      have hVunit : PUnit.unit ∈ (show Set PUnit from V) := by
        exact hUVset hUunit
      exact punit_set_univ_of_unit_mem hVunit
    · intro U V hU hV
      change (U : Set PUnit) = Set.univ at hU
      change (V : Set PUnit) = Set.univ at hV
      change (show Set PUnit from punitOpenPrelocale.inf U V) = Set.univ
      simpa [punitOpenPrelocale, hU, hV]
    · intro U V hUV
      change (show Set PUnit from punitOpenPrelocale.sup U V) = Set.univ at hUV
      have hUnit :
          PUnit.unit ∈ (show Set PUnit from punitOpenPrelocale.sup U V) := by
        rw [hUV]
        trivial
      have hUnion : PUnit.unit ∈ (show Set PUnit from U) ∪ (show Set PUnit from V) := by
        simpa [punitOpenPrelocale] using hUnit
      rcases hUnion with hU | hV
      · left
        change (U : Set PUnit) = Set.univ
        exact punit_set_univ_of_unit_mem hU
      · right
        change (V : Set PUnit) = Set.univ
        exact punit_set_univ_of_unit_mem hV⟩

private theorem punitSpec_unique (F : Spec punitOpenPrelocale.{u}) :
    F = punitTopSpec := by
  apply Subtype.ext
  ext U
  constructor
  · intro hU
    rcases punit_set_empty_or_univ U with hEmpty | hUniv
    · exact False.elim (F.2.zero_not_mem (by simpa [punitOpenPrelocale, hEmpty] using hU))
    · change (U : Set PUnit) = Set.univ
      exact hUniv
  · intro hU
    have hUniv : U = Set.univ := by
      change (U : Set PUnit) = Set.univ at hU
      exact hU
    simpa [punitOpenPrelocale, hUniv] using F.2.one_mem

/-- The corrected proper-filter spectrum of the unit prelocale is isomorphic to
the unit bifinite domain. -/
private def punitSpecDomainIso :
    SpecDomainIso punitOpenPrelocale.{u} punitBifiniteDomain.{u} where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => punitTopSpec
  left_inv := by
    intro F
    exact (punitSpec_unique F).symm
  right_inv := by
    intro x
    cases x
    rfl
  order_compatible := by
    intro F G
    constructor
    · intro _h
      exact le_rfl
    · intro _h U hU
      simpa [punitSpec_unique F, punitSpec_unique G] using hU

/-- Denotation of the property language for the closed unit type as subsets of
the one-point space. -/
private def punitPropertyDenoteSet :
    PropertyExpr Empty (.one : ClosedTypeExpr) → Set PUnit
  | PropertyExpr.truth => (Set.univ : Set PUnit)
  | PropertyExpr.falsity => (∅ : Set PUnit)
  | PropertyExpr.conj φ ψ => punitPropertyDenoteSet φ ∩ punitPropertyDenoteSet ψ
  | PropertyExpr.disj φ ψ => punitPropertyDenoteSet φ ∪ punitPropertyDenoteSet ψ

/-- Boolean evaluation of closed-unit property expressions. -/
private def punitPropertyTruthValue :
    PropertyExpr Empty (.one : ClosedTypeExpr) → Bool
  | PropertyExpr.truth => true
  | PropertyExpr.falsity => false
  | PropertyExpr.conj φ ψ => punitPropertyTruthValue φ && punitPropertyTruthValue ψ
  | PropertyExpr.disj φ ψ => punitPropertyTruthValue φ || punitPropertyTruthValue ψ

/-- On the one-point interpretation, a unit formula denotes exactly its Boolean
truth value. -/
private theorem punitPropertyDenoteSet_unit_iff :
    ∀ φ : PropertyExpr Empty (.one : ClosedTypeExpr),
      PUnit.unit ∈ punitPropertyDenoteSet φ ↔ punitPropertyTruthValue φ = true
  | PropertyExpr.truth => by
      simp [punitPropertyDenoteSet, punitPropertyTruthValue]
  | PropertyExpr.falsity => by
      simp [punitPropertyDenoteSet, punitPropertyTruthValue]
  | PropertyExpr.conj φ ψ => by
      simp [punitPropertyDenoteSet, punitPropertyTruthValue,
        punitPropertyDenoteSet_unit_iff φ, punitPropertyDenoteSet_unit_iff ψ]
  | PropertyExpr.disj φ ψ => by
      simp [punitPropertyDenoteSet, punitPropertyTruthValue,
        punitPropertyDenoteSet_unit_iff φ, punitPropertyDenoteSet_unit_iff ψ]

/-- Inclusion between closed-unit property denotations is Boolean implication. -/
private theorem punitPropertyDenoteSet_subset_iff
    (φ ψ : PropertyExpr Empty (.one : ClosedTypeExpr)) :
    punitPropertyDenoteSet φ ⊆ punitPropertyDenoteSet ψ ↔
      (punitPropertyTruthValue φ = true → punitPropertyTruthValue ψ = true) := by
  constructor
  · intro h hφ
    exact (punitPropertyDenoteSet_unit_iff ψ).1
      (h ((punitPropertyDenoteSet_unit_iff φ).2 hφ))
  · intro h x hx
    cases x
    exact (punitPropertyDenoteSet_unit_iff ψ).2
      (h ((punitPropertyDenoteSet_unit_iff φ).1 hx))

/-- The base `L(1)` preorder used by the decidability proof is decidable in the
concrete one-point interpretation. -/
private def punitPropertyLanguagePreorder_decidable
    (φ ψ : PropertyExpr Empty (.one : ClosedTypeExpr)) :
    Decidable (punitOpenPrelocale.le (punitPropertyDenoteSet φ) (punitPropertyDenoteSet ψ)) := by
  dsimp [punitOpenPrelocale]
  by_cases h :
      punitPropertyTruthValue φ = true → punitPropertyTruthValue ψ = true
  · exact isTrue ((punitPropertyDenoteSet_subset_iff φ ψ).2 h)
  · exact isFalse (fun hle => h ((punitPropertyDenoteSet_subset_iff φ ψ).1 hle))

/-- The syntactic prelocale for the closed unit type, interpreted in the
one-point prelocale. -/
private def punitPropertyLanguagePrelocale :
    PropertyLanguagePrelocale.{u} (.one : ClosedTypeExpr) where
  prelocale := punitOpenPrelocale
  denote := punitPropertyDenoteSet
  truth_is_one := by
    constructor <;> intro x hx <;>
      simpa [punitPropertyDenoteSet, punitOpenPrelocale] using hx
  falsity_is_zero := by
    constructor <;> intro x hx <;>
      simpa [punitPropertyDenoteSet, punitOpenPrelocale] using hx
  conj_is_inf := by
    intro φ ψ
    constructor <;> intro x hx <;>
      simpa [punitPropertyDenoteSet, punitOpenPrelocale] using hx
  disj_is_sup := by
    intro φ ψ
    constructor <;> intro x hx <;>
      simpa [punitPropertyDenoteSet, punitOpenPrelocale] using hx
  generated_by_properties := by
    intro U
    rcases punit_set_empty_or_univ U with hEmpty | hUniv
    · refine ⟨PropertyExpr.falsity, ?_⟩
      constructor <;> intro x hx <;>
        simpa [punitPropertyDenoteSet, punitOpenPrelocale, hEmpty] using hx
    · refine ⟨PropertyExpr.truth, ?_⟩
      constructor <;> intro x hx <;>
        simpa [punitPropertyDenoteSet, punitOpenPrelocale, hUniv] using hx
  preorder_lattice_rules := by
    refine
      { refl := ?_
        trans := ?_
        le_true := ?_
        conj_intro := ?_
        conj_left := ?_
        conj_right := ?_
        false_le := ?_
        disj_elim := ?_
        le_disj_left := ?_
        le_disj_right := ?_
        distributivity := ?_ }
    · intro φ x hx
      exact hx
    · intro φ ψ χ hφψ hψχ x hx
      exact hψχ (hφψ hx)
    · intro φ x _hx
      simpa [punitPropertyDenoteSet]
    · intro φ ψ₁ ψ₂ hφψ₁ hφψ₂ x hx
      simpa [punitPropertyDenoteSet] using ⟨hφψ₁ hx, hφψ₂ hx⟩
    · intro φ ψ x hx
      have hx' : x ∈ punitPropertyDenoteSet φ ∩ punitPropertyDenoteSet ψ := by
        simpa [punitPropertyDenoteSet] using hx
      exact hx'.1
    · intro φ ψ x hx
      have hx' : x ∈ punitPropertyDenoteSet φ ∩ punitPropertyDenoteSet ψ := by
        simpa [punitPropertyDenoteSet] using hx
      exact hx'.2
    · intro φ x hx
      simpa [punitPropertyDenoteSet] using hx
    · intro φ₁ φ₂ ψ hφ₁ψ hφ₂ψ x hx
      rcases (by simpa [punitPropertyDenoteSet] using hx :
          x ∈ punitPropertyDenoteSet φ₁ ∪ punitPropertyDenoteSet φ₂) with hx | hx
      · exact hφ₁ψ hx
      · exact hφ₂ψ hx
    · intro φ ψ x hx
      simpa [punitPropertyDenoteSet] using
        (Or.inl hx :
          x ∈ punitPropertyDenoteSet φ ∪ punitPropertyDenoteSet ψ)
    · intro φ ψ x hx
      simpa [punitPropertyDenoteSet] using
        (Or.inr hx :
          x ∈ punitPropertyDenoteSet φ ∪ punitPropertyDenoteSet ψ)
    · intro φ ψ χ x hx
      rcases (by simpa [punitPropertyDenoteSet] using hx :
          x ∈ punitPropertyDenoteSet φ ∩
            (punitPropertyDenoteSet ψ ∪ punitPropertyDenoteSet χ)) with
        ⟨hxφ, hxψ | hxχ⟩
      · have hxφψ : x ∈ punitPropertyDenoteSet (PropertyExpr.conj φ ψ) := by
          simpa [punitPropertyDenoteSet] using ⟨hxφ, hxψ⟩
        simpa [punitPropertyDenoteSet] using
          (Or.inl hxφψ :
            x ∈
              punitPropertyDenoteSet (PropertyExpr.conj φ ψ) ∪
                punitPropertyDenoteSet (PropertyExpr.conj φ χ))
      · have hxφχ : x ∈ punitPropertyDenoteSet (PropertyExpr.conj φ χ) := by
          simpa [punitPropertyDenoteSet] using ⟨hxφ, hxχ⟩
        simpa [punitPropertyDenoteSet] using
          (Or.inr hxφχ :
            x ∈
              punitPropertyDenoteSet (PropertyExpr.conj φ ψ) ∪
                punitPropertyDenoteSet (PropertyExpr.conj φ χ))

/-- The two interpretations of type expressions and the constructor equations
displayed in the PDF.  This is input data for Theorem 7.3.15; it deliberately
does not contain the theorem's conclusion. -/
structure TypeInterpretationData (Var : Type u) where
  localicEnv : Var → DomainPrelocale.{u}
  domainEnv : Var → Chapter4.BifiniteDomain.{u}
  localicInterpretation : TypeExpr Var → DomainPrelocale.{u}
  domainInterpretation : TypeExpr Var → Chapter4.BifiniteDomain.{u}
  one_localic_clause :
    localicInterpretation .one = punitOpenPrelocale.{u}
  one_domain_clause :
    domainInterpretation .one = punitBifiniteDomain.{u}
  one_describes :
    Nonempty (LocalicDescription (localicInterpretation .one) (domainInterpretation .one))
  var_localic_clause :
    ∀ X : Var, localicInterpretation (.var X) = localicEnv X
  var_domain_clause :
    ∀ X : Var, domainInterpretation (.var X) = domainEnv X
  function_space_localic_clause :
    ∀ σ τ : TypeExpr Var,
      ∃ F : FunctionSpacePrelocaleDescription
          (localicInterpretation σ) (localicInterpretation τ),
        F.prelocale = localicInterpretation (.arr σ τ)
  function_space_domain_clause :
    ∀ σ τ : TypeExpr Var,
      (domainInterpretation (.arr σ τ)).object =
        Chapter4.OrderedDomain.functionSpace
          (domainInterpretation σ).object (domainInterpretation τ).object
  product_localic_clause :
    ∀ σ τ : TypeExpr Var,
      Nonempty (LocalicDescription
        (localicInterpretation (.prod σ τ)) (domainInterpretation (.prod σ τ)))
  product_domain_clause :
    ∀ σ τ : TypeExpr Var,
      (domainInterpretation (.prod σ τ)).object =
        Chapter4.OrderedDomain.prod
          (domainInterpretation σ).object (domainInterpretation τ).object
  sum_localic_clause :
    ∀ σ τ : TypeExpr Var,
      Nonempty (LocalicDescription
        (localicInterpretation (.sum σ τ)) (domainInterpretation (.sum σ τ)))
  lift_localic_clause :
    ∀ σ : TypeExpr Var,
      Nonempty (LocalicDescription
        (localicInterpretation (.lift σ)) (domainInterpretation (.lift σ)))
  plotkin_localic_clause :
    ∀ σ : TypeExpr Var,
      ∃ P : PlotkinPowerlocaleDescription (localicInterpretation σ),
        P.prelocale = localicInterpretation (.plotkin σ)
  plotkin_domain_clause :
    ∀ σ : TypeExpr Var,
      ∃ R : PlotkinLensRepresentation (domainInterpretation σ).object,
        R.powerdomain.carrier = (domainInterpretation (.plotkin σ)).object
  recursive_localic_clause :
    ∀ X : Var, ∀ σ : TypeExpr Var,
      ∃ C : PrelocaleChain.{u}, ∃ B : PrelocaleChainBilimitDescription C,
        B.union = localicInterpretation (.recTy X σ) ∧
          B.bilimit_domain = domainInterpretation (.recTy X σ)

/-- Compatibility wrapper retained for clients that need both the constructor
data and an already established description theorem.  Numbered Theorem 7.3.15
does not take this wrapper as input. -/
structure TypeInterpretationAgreement (Var : Type u) extends
    TypeInterpretationData Var where
  env_describes :
    ∀ X : Var, Nonempty (LocalicDescription (localicEnv X) (domainEnv X))
  interpretations_describe :
    ∀ σ : TypeExpr Var,
      Nonempty (LocalicDescription (localicInterpretation σ) (domainInterpretation σ))

/-- Closed-type specialization of the interpretation clauses, avoiding a universe
collapse through `Empty` environments while still tying closed syntactic
prelocales to the corresponding bifinite-domain interpretation. -/
structure ClosedTypeInterpretationAgreement where
  localicInterpretation : ClosedTypeExpr → DomainPrelocale.{u}
  domainInterpretation : ClosedTypeExpr → Chapter4.BifiniteDomain.{u}
  one_localic_clause :
    localicInterpretation .one = punitOpenPrelocale.{u}
  one_domain_clause :
    domainInterpretation .one = punitBifiniteDomain.{u}
  function_space_localic_clause :
    ∀ σ τ : ClosedTypeExpr,
      ∃ F : FunctionSpacePrelocaleDescription
          (localicInterpretation σ) (localicInterpretation τ),
        F.prelocale = localicInterpretation (.arr σ τ)
  function_space_domain_clause :
    ∀ σ τ : ClosedTypeExpr,
      (domainInterpretation (.arr σ τ)).object =
        Chapter4.OrderedDomain.functionSpace
          (domainInterpretation σ).object (domainInterpretation τ).object
  product_localic_clause :
    ∀ σ τ : ClosedTypeExpr,
      Nonempty (LocalicDescription
        (localicInterpretation (.prod σ τ)) (domainInterpretation (.prod σ τ)))
  product_domain_clause :
    ∀ σ τ : ClosedTypeExpr,
      (domainInterpretation (.prod σ τ)).object =
        Chapter4.OrderedDomain.prod
          (domainInterpretation σ).object (domainInterpretation τ).object
  sum_localic_clause :
    ∀ σ τ : ClosedTypeExpr,
      Nonempty (LocalicDescription
        (localicInterpretation (.sum σ τ)) (domainInterpretation (.sum σ τ)))
  lift_localic_clause :
    ∀ σ : ClosedTypeExpr,
      Nonempty (LocalicDescription
        (localicInterpretation (.lift σ)) (domainInterpretation (.lift σ)))
  plotkin_localic_clause :
    ∀ σ : ClosedTypeExpr,
      ∃ P : PlotkinPowerlocaleDescription (localicInterpretation σ),
        P.prelocale = localicInterpretation (.plotkin σ)
  plotkin_domain_clause :
    ∀ σ : ClosedTypeExpr,
      ∃ R : PlotkinLensRepresentation (domainInterpretation σ).object,
        R.powerdomain.carrier = (domainInterpretation (.plotkin σ)).object
  interpretations_describe :
    ∀ σ : ClosedTypeExpr,
      Nonempty (LocalicDescription (localicInterpretation σ) (domainInterpretation σ))

/-- Source-facing spectrum package for a closed type expression over an
arbitrary supply of binder names.  Closedness is a proof about free variables,
so recursive types need not be forced into the uninhabited `Empty` fragment. -/
structure ClosedTypeSpectrumDescriptionFor
    {Var : Type u} (σ : TypeExpr Var) (_hσ : TypeExpr.IsClosed σ) where
  prelocale : DomainPrelocale.{u}
  domain : Chapter4.BifiniteDomain.{u}
  property_language : PropertyLanguagePrelocale.{u} σ
  prelocale_eq_property_language : prelocale = property_language.prelocale
  describes : Nonempty (LocalicDescription prelocale domain)
  spectrum_iso : Nonempty (SpecDomainIso prelocale domain)
  interpretation_data :
    ∃ ρ : TypeInterpretationData Var,
      (∀ X : Var,
        Nonempty (LocalicDescription (ρ.localicEnv X) (ρ.domainEnv X))) ∧
        ρ.localicInterpretation σ = prelocale ∧
          ρ.domainInterpretation σ = domain

/-- The localic spectrum description of the current closed-fragment expression.
The returned
prelocale is explicitly tied to the syntactic property language `L(σ)` and to
closed localic/domain interpretations of the same expression. -/
structure ClosedTypeSpectrumDescription (σ : ClosedTypeExpr) where
  prelocale : DomainPrelocale.{u}
  domain : Chapter4.BifiniteDomain.{u}
  property_language : PropertyLanguagePrelocale.{u} σ
  prelocale_eq_property_language : prelocale = property_language.prelocale
  describes : Nonempty (LocalicDescription prelocale domain)
  spectrum_iso : Nonempty (SpecDomainIso prelocale domain)
  closed_interpretation_agreement :
    ∃ ρ : ClosedTypeInterpretationAgreement.{u},
      ρ.localicInterpretation σ = prelocale ∧
        ρ.domainInterpretation σ = domain ∧
          Nonempty (LocalicDescription
            (ρ.localicInterpretation σ) (ρ.domainInterpretation σ))

/-- The closed unit type has the expected localic spectrum package once a
closed-type interpretation agreement is supplied.  This isolates the base case
of Theorem 7.3.16 without asserting the missing recursive/product/function-space
constructions for every closed type. -/
theorem closedTypeSpectrumDescription_one_of_agreement
    (ρ : ClosedTypeInterpretationAgreement.{u}) :
    Nonempty (ClosedTypeSpectrumDescription.{u} (.one : ClosedTypeExpr)) := by
  refine ⟨{
    prelocale := punitOpenPrelocale
    domain := punitBifiniteDomain
    property_language := punitPropertyLanguagePrelocale
    prelocale_eq_property_language := rfl
    describes := ⟨punitLocalicDescription⟩
    spectrum_iso := ⟨punitSpecDomainIso⟩
    closed_interpretation_agreement := ?_ }⟩
  refine ⟨ρ, ρ.one_localic_clause, ρ.one_domain_clause, ?_⟩
  rw [ρ.one_localic_clause, ρ.one_domain_clause]
  exact ⟨punitLocalicDescription⟩


end Chapter7
end AbramskyJung

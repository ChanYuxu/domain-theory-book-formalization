import Practice.DomainTheory.Chapter07.Section73.Syntax

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 7.3: domain-logic derivations

This module follows one coherent dependency cluster inside the textbook
section. The stable public import remains
`Practice.DomainTheory.Chapter07.Section73`.
-/

universe u v

namespace AbramskyJung
namespace Chapter7

/-- Explicit derivation syntax for the main displayed domain-logic rules.  This
records the rule shapes separately from the semantic soundness/completeness
package below. -/
inductive DomainLogicDerivation (Var : Type u) : PropertySequent Var → Prop where
  | truth
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} (M : TermExpr Var σ) :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.truth : PropertyExpr Var σ))
  | variable
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      (a : PropertyAssumption Var) (_ha : a ∈ Γ) :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ
          (TermExpr.typedVar (σ := a.σ) a.varName) a.property)
  | bottom
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ (TermExpr.bottom : TermExpr Var σ)
          (PropertyExpr.truth : PropertyExpr Var σ))
  | structural_weakening {s : PropertySequent Var}
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ) :
      (∀ a : PropertyAssumption Var, a ∈ s.context → a ∈ Γ) →
        DomainLogicDerivation Var s →
          DomainLogicDerivation Var (PropertySequent.withContext s Γ hΓ)
  | preorder {s : PropertySequent Var} {ψ : PropertyExpr Var s.σ} :
      DomainLogicDerivation Var s →
        PropertyFormulaPreorder Var s.property ψ →
          DomainLogicDerivation Var (PropertySequent.withProperty s ψ)
  | conj_intro {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ} :
      DomainLogicDerivation Var (PropertySequent.withProperty s φ) →
        DomainLogicDerivation Var (PropertySequent.withProperty s ψ) →
          DomainLogicDerivation Var
            (PropertySequent.withProperty s (PropertyExpr.conj φ ψ))
  | disj_left {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ} :
      DomainLogicDerivation Var (PropertySequent.withProperty s φ) →
        DomainLogicDerivation Var
          (PropertySequent.withProperty s (PropertyExpr.disj φ ψ))
  | disj_right {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ} :
      DomainLogicDerivation Var (PropertySequent.withProperty s ψ) →
        DomainLogicDerivation Var
          (PropertySequent.withProperty s (PropertyExpr.disj φ ψ))
  | lam
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var} {M : TermExpr Var τ}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M ψ) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ (TermExpr.lam (σ := σ) M)
            (PropertyExpr.arrow φ ψ))
  | app
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var} {M : TermExpr Var (.arr σ τ)} {N : TermExpr Var σ}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.arrow φ ψ)) →
        DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ N φ) →
          DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ (TermExpr.app M N) ψ)
  | pair
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var} {M : TermExpr Var σ} {N : TermExpr Var τ}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M φ) →
        DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ N ψ) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.pair M N)
              (PropertyExpr.product φ ψ))
  | let_pair
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ ν : TypeExpr Var}
      {M : TermExpr Var (.prod σ τ)} {N : TermExpr Var ν}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ}
      {χ : PropertyExpr Var ν} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.product φ ψ)) →
        DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ N χ) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.letPair M N) χ)
  | inl
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var} {M : TermExpr Var σ} {φ : PropertyExpr Var σ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M φ) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ (TermExpr.inl (τ := τ) M)
            (PropertyExpr.sumLeft (τ := τ) φ))
  | inr
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var} {M : TermExpr Var τ} {φ : PropertyExpr Var τ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M φ) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ (TermExpr.inr (σ := σ) M)
            (PropertyExpr.sumRight (σ := σ) φ))
  | case_sum
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ ν : TypeExpr Var}
      {M : TermExpr Var (.sum σ τ)} {N P : TermExpr Var ν}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ}
      {χ : PropertyExpr Var ν} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M
          (PropertyExpr.disj
            (PropertyExpr.sumLeft (τ := τ) φ)
            (PropertyExpr.sumRight (σ := σ) ψ))) →
        DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ N χ) →
        DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ P χ) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.caseSum M N P) χ)
  | up
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} {M : TermExpr Var σ} {φ : PropertyExpr Var σ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M φ) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ (TermExpr.up M) (PropertyExpr.lifted φ))
  | lift_elim
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var} {M : TermExpr Var (.lift σ)} {N : TermExpr Var τ}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.lifted φ)) →
        DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ N ψ) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.liftElim M N) ψ)
  | singleton_box
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} {M : TermExpr Var σ} {φ : PropertyExpr Var σ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M φ) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ (TermExpr.singleton M) (PropertyExpr.box φ))
  | singleton_diamond
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} {M : TermExpr Var σ} {φ : PropertyExpr Var σ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M φ) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ (TermExpr.singleton M) (PropertyExpr.diamond φ))
  | over_box
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var}
      {M : TermExpr Var (.plotkin σ)} {N : TermExpr Var (.plotkin τ)}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.diamond φ)) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ N (PropertyExpr.box ψ)) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.over M N) (PropertyExpr.box ψ))
  | over_diamond
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var}
      {M : TermExpr Var (.plotkin σ)} {N : TermExpr Var (.plotkin τ)}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.diamond φ)) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ N (PropertyExpr.diamond ψ)) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.over M N) (PropertyExpr.diamond ψ))
  | union_box
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} {M N : TermExpr Var (.plotkin σ)}
      {φ : PropertyExpr Var σ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.box φ)) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ N (PropertyExpr.box φ)) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.union M N) (PropertyExpr.box φ))
  | union_diamond_left
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} {M N : TermExpr Var (.plotkin σ)}
      {φ : PropertyExpr Var σ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.diamond φ)) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.union M N) (PropertyExpr.diamond φ))
  | union_diamond_right
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} {M N : TermExpr Var (.plotkin σ)}
      {φ : PropertyExpr Var σ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ N (PropertyExpr.diamond φ)) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.union M N) (PropertyExpr.diamond φ))
  | tensor_box
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var}
      {M : TermExpr Var (.plotkin σ)} {N : TermExpr Var (.plotkin τ)}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.box φ)) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ N (PropertyExpr.box ψ)) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.tensor M N)
              (PropertyExpr.box (PropertyExpr.product φ ψ)))
  | tensor_diamond
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var}
      {M : TermExpr Var (.plotkin σ)} {N : TermExpr Var (.plotkin τ)}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.diamond φ)) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ N (PropertyExpr.diamond ψ)) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.tensor M N)
              (PropertyExpr.diamond (PropertyExpr.product φ ψ)))
  | fold
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {X : Var} {σ τ : TypeExpr Var} {hrec : TypeExpr.RecUnfolding X σ τ}
      {M : TermExpr Var τ} {φ : PropertyExpr Var τ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M φ) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ (TermExpr.fold hrec M)
            (PropertyExpr.recProp hrec φ))
  | unfold
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {X : Var} {σ τ : TypeExpr Var} {hrec : TypeExpr.RecUnfolding X σ τ}
      {M : TermExpr Var (.recTy X σ)} {φ : PropertyExpr Var τ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.recProp hrec φ)) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ (TermExpr.unfold hrec M) φ)
  | fixpoint
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} {M : TermExpr Var σ} {φ : PropertyExpr Var σ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M φ) →
        DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ (TermExpr.mu M) φ)

/-- Derived form of structural weakening for an arbitrary supercontext. -/
theorem DomainLogicDerivation.weaken_context {Var : Type u}
    {s : PropertySequent Var}
    {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
    (hsub : ∀ a : PropertyAssumption Var, a ∈ s.context → a ∈ Γ) :
    DomainLogicDerivation Var s →
      DomainLogicDerivation Var (PropertySequent.withContext s Γ hΓ) := by
  intro hs
  exact DomainLogicDerivation.structural_weakening hΓ hsub hs

/-- Derived weakening that extends a sequent by one fresh assumption. -/
theorem DomainLogicDerivation.weaken_cons {Var : Type u}
    {s : PropertySequent Var} {a : PropertyAssumption Var}
    (hfresh :
      ∀ b : PropertyAssumption Var, b ∈ s.context →
        a.σ = b.σ → a.varName = b.varName → False) :
    DomainLogicDerivation Var s →
      DomainLogicDerivation Var
        (PropertySequent.withContext s (a :: s.context)
          (PropertyContextFunctional.cons s.context_functional hfresh)) := by
  intro hs
  exact
    DomainLogicDerivation.weaken_context
      (PropertyContextFunctional.cons s.context_functional hfresh)
      (by
        intro b hb
        simp [hb]) hs

/-- Derived conjunction introduction after formula-preorder weakening of each
conjunct. -/
theorem DomainLogicDerivation.conj_intro_preorder {Var : Type u}
    {s : PropertySequent Var} {φ φ' ψ ψ' : PropertyExpr Var s.σ}
    (hφ : DomainLogicDerivation Var (PropertySequent.withProperty s φ))
    (hψ : DomainLogicDerivation Var (PropertySequent.withProperty s ψ))
    (hφ' : PropertyFormulaPreorder Var φ φ')
    (hψ' : PropertyFormulaPreorder Var ψ ψ') :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj φ' ψ')) := by
  have dφ' :
      DomainLogicDerivation Var (PropertySequent.withProperty s φ') := by
    simpa [PropertySequent.withProperty] using
      (DomainLogicDerivation.preorder hφ hφ')
  have dψ' :
      DomainLogicDerivation Var (PropertySequent.withProperty s ψ') := by
    simpa [PropertySequent.withProperty] using
      (DomainLogicDerivation.preorder hψ hψ')
  exact DomainLogicDerivation.conj_intro dφ' dψ'

/-- Derived transport across commutativity of conjunction. -/
theorem DomainLogicDerivation.conj_comm {Var : Type u}
    {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj φ ψ))) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj ψ φ)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h (PropertyFormulaPreorder.conj_comm φ ψ))

/-- Derived transport across commutativity of disjunction. -/
theorem DomainLogicDerivation.disj_comm {Var : Type u}
    {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj φ ψ))) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj ψ φ)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h (PropertyFormulaPreorder.disj_comm φ ψ))

/-- A derivation of one listed disjunct derives the finite disjunction. -/
theorem DomainLogicDerivation.finiteDisj_of_mem {Var : Type u}
    {s : PropertySequent Var} {l : List (PropertyExpr Var s.σ)}
    {φ : PropertyExpr Var s.σ}
    (hmem : φ ∈ l)
    (hφ : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.finiteDisj l)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder hφ
      (PropertyFormulaPreorder.le_finiteDisj_of_mem hmem))

/-- A finite-disjunction derivation can be eliminated along a formula-preorder
upper bound for every listed disjunct. -/
theorem DomainLogicDerivation.finiteDisj_elim_preorder {Var : Type u}
    {s : PropertySequent Var} {l : List (PropertyExpr Var s.σ)}
    {ψ : PropertyExpr Var s.σ}
    (hl : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.finiteDisj l)))
    (hψ : ∀ φ : PropertyExpr Var s.σ,
      φ ∈ l → PropertyFormulaPreorder Var φ ψ) :
    DomainLogicDerivation Var (PropertySequent.withProperty s ψ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder hl
      (PropertyFormulaPreorder.finiteDisj_le hψ))

/-- Derived transitive formula-preorder transport for a fixed sequent. -/
theorem DomainLogicDerivation.preorder_trans {Var : Type u}
    {s : PropertySequent Var} {φ ψ χ : PropertyExpr Var s.σ}
    (hφ : DomainLogicDerivation Var (PropertySequent.withProperty s φ))
    (hφψ : PropertyFormulaPreorder Var φ ψ)
    (hψχ : PropertyFormulaPreorder Var ψ χ) :
    DomainLogicDerivation Var (PropertySequent.withProperty s χ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder hφ
      (PropertyFormulaPreorder.trans hφψ hψχ))

/-- Derived conjunction-left elimination for displayed derivations. -/
theorem DomainLogicDerivation.conj_left {Var : Type u}
    {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj φ ψ))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.conj_left φ ψ))

/-- Derived conjunction-right elimination for displayed derivations. -/
theorem DomainLogicDerivation.conj_right {Var : Type u}
    {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj φ ψ))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s ψ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.conj_right φ ψ))

/-- Derived left disjunction introduction after formula-preorder weakening. -/
theorem DomainLogicDerivation.disj_left_preorder {Var : Type u}
    {s : PropertySequent Var} {φ φ' ψ : PropertyExpr Var s.σ}
    (hφ : DomainLogicDerivation Var (PropertySequent.withProperty s φ))
    (hφ' : PropertyFormulaPreorder Var φ φ') :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj φ' ψ)) := by
  exact
    DomainLogicDerivation.preorder_trans hφ hφ'
      (PropertyFormulaPreorder.le_disj_left φ' ψ)

/-- Derived right disjunction introduction after formula-preorder weakening. -/
theorem DomainLogicDerivation.disj_right_preorder {Var : Type u}
    {s : PropertySequent Var} {φ ψ ψ' : PropertyExpr Var s.σ}
    (hψ : DomainLogicDerivation Var (PropertySequent.withProperty s ψ))
    (hψ' : PropertyFormulaPreorder Var ψ ψ') :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj φ ψ')) := by
  exact
    DomainLogicDerivation.preorder_trans hψ hψ'
      (PropertyFormulaPreorder.le_disj_right φ ψ')

/-- Truth is derivable for any displayed sequent shape with the same context
and term. -/
theorem DomainLogicDerivation.truth_intro {Var : Type u}
    (s : PropertySequent Var) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.truth : PropertyExpr Var s.σ)) := by
  simpa [PropertySequent.withProperty, PropertySequent.ofTerm] using
    (DomainLogicDerivation.truth s.context_functional s.term)

/-- Falsity entails every formula in the displayed derivation preorder. -/
theorem DomainLogicDerivation.false_elim {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (hfalse : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.falsity : PropertyExpr Var s.σ))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder hfalse
      (PropertyFormulaPreorder.false_le φ))

/-- Derived conjunction monotonicity for displayed derivations. -/
theorem DomainLogicDerivation.conj_mono {Var : Type u}
    {s : PropertySequent Var} {φ φ' ψ ψ' : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj φ ψ)))
    (hφ : PropertyFormulaPreorder Var φ φ')
    (hψ : PropertyFormulaPreorder Var ψ ψ') :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj φ' ψ')) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.conj_mono hφ hψ))

/-- Derived disjunction monotonicity for displayed derivations. -/
theorem DomainLogicDerivation.disj_mono {Var : Type u}
    {s : PropertySequent Var} {φ φ' ψ ψ' : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj φ ψ)))
    (hφ : PropertyFormulaPreorder Var φ φ')
    (hψ : PropertyFormulaPreorder Var ψ ψ') :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj φ' ψ')) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.disj_mono hφ hψ))

/-- Derived binary disjunction elimination along a common formula-preorder
upper bound. -/
theorem DomainLogicDerivation.disj_elim_preorder {Var : Type u}
    {s : PropertySequent Var} {φ ψ χ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj φ ψ)))
    (hφ : PropertyFormulaPreorder Var φ χ)
    (hψ : PropertyFormulaPreorder Var ψ χ) :
    DomainLogicDerivation Var (PropertySequent.withProperty s χ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.disj_elim hφ hψ))

/-- Derived distributivity transport for displayed derivations. -/
theorem DomainLogicDerivation.distributivity {Var : Type u}
    {s : PropertySequent Var} {φ ψ χ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj φ (PropertyExpr.disj ψ χ)))) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj (PropertyExpr.conj φ ψ)
          (PropertyExpr.conj φ χ))) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.distributivity φ ψ χ))

/-- Conjunction is associative in the generated formula preorder. -/
theorem PropertyFormulaPreorder.conj_assoc {Var : Type u} {σ : TypeExpr Var}
    (φ ψ χ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.conj (PropertyExpr.conj φ ψ) χ)
      (PropertyExpr.conj φ (PropertyExpr.conj ψ χ)) := by
  exact
    PropertyFormulaPreorder.conj_intro
      (PropertyFormulaPreorder.trans
        (PropertyFormulaPreorder.conj_left (PropertyExpr.conj φ ψ) χ)
        (PropertyFormulaPreorder.conj_left φ ψ))
      (PropertyFormulaPreorder.conj_intro
        (PropertyFormulaPreorder.trans
          (PropertyFormulaPreorder.conj_left (PropertyExpr.conj φ ψ) χ)
          (PropertyFormulaPreorder.conj_right φ ψ))
        (PropertyFormulaPreorder.conj_right (PropertyExpr.conj φ ψ) χ))

/-- Conjunction associativity in the reverse generated-preorder direction. -/
theorem PropertyFormulaPreorder.conj_assoc_symm {Var : Type u}
    {σ : TypeExpr Var} (φ ψ χ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.conj φ (PropertyExpr.conj ψ χ))
      (PropertyExpr.conj (PropertyExpr.conj φ ψ) χ) := by
  exact
    PropertyFormulaPreorder.conj_intro
      (PropertyFormulaPreorder.conj_intro
        (PropertyFormulaPreorder.conj_left φ (PropertyExpr.conj ψ χ))
        (PropertyFormulaPreorder.trans
          (PropertyFormulaPreorder.conj_right φ (PropertyExpr.conj ψ χ))
          (PropertyFormulaPreorder.conj_left ψ χ)))
      (PropertyFormulaPreorder.trans
        (PropertyFormulaPreorder.conj_right φ (PropertyExpr.conj ψ χ))
        (PropertyFormulaPreorder.conj_right ψ χ))

/-- Disjunction is associative in the generated formula preorder. -/
theorem PropertyFormulaPreorder.disj_assoc {Var : Type u} {σ : TypeExpr Var}
    (φ ψ χ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.disj (PropertyExpr.disj φ ψ) χ)
      (PropertyExpr.disj φ (PropertyExpr.disj ψ χ)) := by
  exact
    PropertyFormulaPreorder.disj_elim
      (PropertyFormulaPreorder.disj_elim
        (PropertyFormulaPreorder.le_disj_left φ (PropertyExpr.disj ψ χ))
        (PropertyFormulaPreorder.trans
          (PropertyFormulaPreorder.le_disj_left ψ χ)
          (PropertyFormulaPreorder.le_disj_right φ (PropertyExpr.disj ψ χ))))
      (PropertyFormulaPreorder.trans
        (PropertyFormulaPreorder.le_disj_right ψ χ)
        (PropertyFormulaPreorder.le_disj_right φ (PropertyExpr.disj ψ χ)))

/-- Disjunction associativity in the reverse generated-preorder direction. -/
theorem PropertyFormulaPreorder.disj_assoc_symm {Var : Type u}
    {σ : TypeExpr Var} (φ ψ χ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.disj φ (PropertyExpr.disj ψ χ))
      (PropertyExpr.disj (PropertyExpr.disj φ ψ) χ) := by
  exact
    PropertyFormulaPreorder.disj_elim
      (PropertyFormulaPreorder.trans
        (PropertyFormulaPreorder.le_disj_left φ ψ)
        (PropertyFormulaPreorder.le_disj_left (PropertyExpr.disj φ ψ) χ))
      (PropertyFormulaPreorder.disj_elim
        (PropertyFormulaPreorder.trans
          (PropertyFormulaPreorder.le_disj_right φ ψ)
          (PropertyFormulaPreorder.le_disj_left (PropertyExpr.disj φ ψ) χ))
        (PropertyFormulaPreorder.le_disj_right (PropertyExpr.disj φ ψ) χ))

/-- Conjunction idempotence in the generated formula preorder. -/
theorem PropertyFormulaPreorder.conj_idem {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var (PropertyExpr.conj φ φ) φ := by
  exact PropertyFormulaPreorder.conj_left φ φ

/-- A formula is below its self-conjunction in the generated formula preorder. -/
theorem PropertyFormulaPreorder.le_conj_self {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var φ (PropertyExpr.conj φ φ) := by
  exact
    PropertyFormulaPreorder.conj_intro
      (PropertyFormulaPreorder.refl φ) (PropertyFormulaPreorder.refl φ)

/-- Disjunction idempotence in the generated formula preorder. -/
theorem PropertyFormulaPreorder.disj_idem {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var (PropertyExpr.disj φ φ) φ := by
  exact
    PropertyFormulaPreorder.disj_elim
      (PropertyFormulaPreorder.refl φ) (PropertyFormulaPreorder.refl φ)

/-- A formula is below its self-disjunction in the generated formula preorder. -/
theorem PropertyFormulaPreorder.le_disj_self {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var φ (PropertyExpr.disj φ φ) := by
  exact PropertyFormulaPreorder.le_disj_left φ φ

/-- Derived conjunction associativity transport for displayed derivations. -/
theorem DomainLogicDerivation.conj_assoc {Var : Type u}
    {s : PropertySequent Var} {φ ψ χ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj (PropertyExpr.conj φ ψ) χ))) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj φ (PropertyExpr.conj ψ χ))) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.conj_assoc φ ψ χ))

/-- Derived reverse conjunction associativity transport for displayed
derivations. -/
theorem DomainLogicDerivation.conj_assoc_symm {Var : Type u}
    {s : PropertySequent Var} {φ ψ χ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj φ (PropertyExpr.conj ψ χ)))) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj (PropertyExpr.conj φ ψ) χ)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.conj_assoc_symm φ ψ χ))

/-- Derived disjunction associativity transport for displayed derivations. -/
theorem DomainLogicDerivation.disj_assoc {Var : Type u}
    {s : PropertySequent Var} {φ ψ χ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj (PropertyExpr.disj φ ψ) χ))) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj φ (PropertyExpr.disj ψ χ))) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.disj_assoc φ ψ χ))

/-- Derived reverse disjunction associativity transport for displayed
derivations. -/
theorem DomainLogicDerivation.disj_assoc_symm {Var : Type u}
    {s : PropertySequent Var} {φ ψ χ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj φ (PropertyExpr.disj ψ χ)))) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj (PropertyExpr.disj φ ψ) χ)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.disj_assoc_symm φ ψ χ))

/-- Derived conjunction idempotence transport for displayed derivations. -/
theorem DomainLogicDerivation.conj_idem {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj φ φ))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.conj_idem φ))

/-- A derivation can be duplicated into a self-conjunction. -/
theorem DomainLogicDerivation.conj_intro_self {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj φ φ)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.le_conj_self φ))

/-- Derived disjunction idempotence transport for displayed derivations. -/
theorem DomainLogicDerivation.disj_idem {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj φ φ))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.disj_idem φ))

/-- A derivation can be injected into a self-disjunction. -/
theorem DomainLogicDerivation.disj_intro_self {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj φ φ)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.le_disj_self φ))

/-- Conjunction absorbs a disjunction containing the left conjunct. -/
theorem PropertyFormulaPreorder.conj_absorb {Var : Type u} {σ : TypeExpr Var}
    (φ ψ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.conj φ (PropertyExpr.disj φ ψ)) φ := by
  exact PropertyFormulaPreorder.conj_left φ (PropertyExpr.disj φ ψ)

/-- A formula is below its conjunction with a disjunction containing itself. -/
theorem PropertyFormulaPreorder.le_conj_absorb {Var : Type u}
    {σ : TypeExpr Var} (φ ψ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var φ
      (PropertyExpr.conj φ (PropertyExpr.disj φ ψ)) := by
  exact
    PropertyFormulaPreorder.conj_intro
      (PropertyFormulaPreorder.refl φ)
      (PropertyFormulaPreorder.le_disj_left φ ψ)

/-- Disjunction absorbs a conjunction containing the left disjunct. -/
theorem PropertyFormulaPreorder.disj_absorb {Var : Type u} {σ : TypeExpr Var}
    (φ ψ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.disj φ (PropertyExpr.conj φ ψ)) φ := by
  exact
    PropertyFormulaPreorder.disj_elim
      (PropertyFormulaPreorder.refl φ)
      (PropertyFormulaPreorder.conj_left φ ψ)

/-- A formula is below its disjunction with a conjunction containing itself. -/
theorem PropertyFormulaPreorder.le_disj_absorb {Var : Type u}
    {σ : TypeExpr Var} (φ ψ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var φ
      (PropertyExpr.disj φ (PropertyExpr.conj φ ψ)) := by
  exact PropertyFormulaPreorder.le_disj_left φ (PropertyExpr.conj φ ψ)

/-- Derived conjunction absorption transport for displayed derivations. -/
theorem DomainLogicDerivation.conj_absorb {Var : Type u}
    {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj φ (PropertyExpr.disj φ ψ)))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.conj_absorb φ ψ))

/-- A displayed derivation can be expanded by conjunction absorption. -/
theorem DomainLogicDerivation.conj_intro_absorb {Var : Type u}
    {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj φ (PropertyExpr.disj φ ψ))) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.le_conj_absorb φ ψ))

/-- Derived disjunction absorption transport for displayed derivations. -/
theorem DomainLogicDerivation.disj_absorb {Var : Type u}
    {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj φ (PropertyExpr.conj φ ψ)))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.disj_absorb φ ψ))

/-- A displayed derivation can be expanded by disjunction absorption. -/
theorem DomainLogicDerivation.disj_intro_absorb {Var : Type u}
    {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj φ (PropertyExpr.conj φ ψ))) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.le_disj_absorb φ ψ))

/-- Truth is a right unit for conjunction in the generated formula preorder. -/
theorem PropertyFormulaPreorder.conj_truth {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.conj φ (PropertyExpr.truth : PropertyExpr Var σ)) φ := by
  exact
    PropertyFormulaPreorder.conj_left φ
      (PropertyExpr.truth : PropertyExpr Var σ)

/-- A formula is below its conjunction with truth on the right. -/
theorem PropertyFormulaPreorder.le_conj_truth {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var φ
      (PropertyExpr.conj φ (PropertyExpr.truth : PropertyExpr Var σ)) := by
  exact
    PropertyFormulaPreorder.conj_intro
      (PropertyFormulaPreorder.refl φ)
      (PropertyFormulaPreorder.le_true φ)

/-- Truth is a left unit for conjunction in the generated formula preorder. -/
theorem PropertyFormulaPreorder.truth_conj {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.conj (PropertyExpr.truth : PropertyExpr Var σ) φ) φ := by
  exact
    PropertyFormulaPreorder.conj_right
      (PropertyExpr.truth : PropertyExpr Var σ) φ

/-- A formula is below its conjunction with truth on the left. -/
theorem PropertyFormulaPreorder.le_truth_conj {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var φ
      (PropertyExpr.conj (PropertyExpr.truth : PropertyExpr Var σ) φ) := by
  exact
    PropertyFormulaPreorder.conj_intro
      (PropertyFormulaPreorder.le_true φ)
      (PropertyFormulaPreorder.refl φ)

/-- Falsity is a right unit for disjunction in the generated formula preorder. -/
theorem PropertyFormulaPreorder.disj_falsity {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.disj φ (PropertyExpr.falsity : PropertyExpr Var σ)) φ := by
  exact
    PropertyFormulaPreorder.disj_elim
      (PropertyFormulaPreorder.refl φ)
      (PropertyFormulaPreorder.false_le φ)

/-- A formula is below its disjunction with falsity on the right. -/
theorem PropertyFormulaPreorder.le_disj_falsity {Var : Type u}
    {σ : TypeExpr Var} (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var φ
      (PropertyExpr.disj φ (PropertyExpr.falsity : PropertyExpr Var σ)) := by
  exact
    PropertyFormulaPreorder.le_disj_left φ
      (PropertyExpr.falsity : PropertyExpr Var σ)

/-- Falsity is a left unit for disjunction in the generated formula preorder. -/
theorem PropertyFormulaPreorder.falsity_disj {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.disj (PropertyExpr.falsity : PropertyExpr Var σ) φ) φ := by
  exact
    PropertyFormulaPreorder.disj_elim
      (PropertyFormulaPreorder.false_le φ)
      (PropertyFormulaPreorder.refl φ)

/-- A formula is below its disjunction with falsity on the left. -/
theorem PropertyFormulaPreorder.le_falsity_disj {Var : Type u}
    {σ : TypeExpr Var} (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var φ
      (PropertyExpr.disj (PropertyExpr.falsity : PropertyExpr Var σ) φ) := by
  exact
    PropertyFormulaPreorder.le_disj_right
      (PropertyExpr.falsity : PropertyExpr Var σ) φ

/-- Derived right-truth conjunction transport for displayed derivations. -/
theorem DomainLogicDerivation.conj_truth {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj φ
          (PropertyExpr.truth : PropertyExpr Var s.σ)))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.conj_truth φ))

/-- A displayed derivation can be expanded by conjoining truth on the right. -/
theorem DomainLogicDerivation.conj_intro_truth {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj φ
          (PropertyExpr.truth : PropertyExpr Var s.σ))) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.le_conj_truth φ))

/-- Derived left-truth conjunction transport for displayed derivations. -/
theorem DomainLogicDerivation.truth_conj {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj
          (PropertyExpr.truth : PropertyExpr Var s.σ) φ))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.truth_conj φ))

/-- A displayed derivation can be expanded by conjoining truth on the left. -/
theorem DomainLogicDerivation.truth_conj_intro {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj
          (PropertyExpr.truth : PropertyExpr Var s.σ) φ)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.le_truth_conj φ))

/-- Derived right-falsity disjunction transport for displayed derivations. -/
theorem DomainLogicDerivation.disj_falsity {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj φ
          (PropertyExpr.falsity : PropertyExpr Var s.σ)))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.disj_falsity φ))

/-- A displayed derivation can be expanded by disjoining falsity on the right. -/
theorem DomainLogicDerivation.disj_intro_falsity {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj φ
          (PropertyExpr.falsity : PropertyExpr Var s.σ))) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.le_disj_falsity φ))

/-- Derived left-falsity disjunction transport for displayed derivations. -/
theorem DomainLogicDerivation.falsity_disj {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj
          (PropertyExpr.falsity : PropertyExpr Var s.σ) φ))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.falsity_disj φ))

/-- A displayed derivation can be expanded by disjoining falsity on the left. -/
theorem DomainLogicDerivation.falsity_disj_intro {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj
          (PropertyExpr.falsity : PropertyExpr Var s.σ) φ)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.le_falsity_disj φ))

/-- Coverage of the sequent-calculus rules displayed before Theorem 7.3.18. -/
structure DomainLogicRuleCoverage (Var : Type u) where
  FormulaFilterSideCondition : {σ : TypeExpr Var} → Set (PropertyExpr Var σ) → Prop
  formula_filter_side_condition_matches_syntax :
    ∀ {σ : TypeExpr Var} (F : Set (PropertyExpr Var σ)),
      FormulaFilterSideCondition F ↔ PropertyFormulaPrimeFilter Var F
  preorder_weakening_rules : Prop
  PrimeContextSideCondition : List (PropertyAssumption Var) → Prop
  prime_context_side_condition_matches_syntax :
    ∀ Γ : List (PropertyAssumption Var),
      PrimeContextSideCondition Γ ↔ PropertyContextPrime Γ
  structural_weakening_rule : Prop
  variable_rule : Prop
  function_rules : Prop
  product_rules : Prop
  sum_and_case_rules : Prop
  lifting_rules : Prop
  plotkin_singleton_and_bind_rules : Prop
  plotkin_union_and_tensor_rules : Prop
  recursive_fold_unfold_rules : Prop
  fixpoint_rule : Prop
  positive_inductive_presentation : Prop

/-- Denotational interpretation data for the displayed domain-logic calculus.
The derivability relation is fixed separately as `DomainLogicDerivation`; it is
not a selectable field of this semantic interface. -/
structure DomainLogicInterpretation (Var : Type u) where
  Environment : Type u
  SatisfiesAssumption : Environment → PropertyAssumption Var → Prop
  TermSatisfiesProperty : Environment → PropertySequent Var → Prop
  rule_coverage : DomainLogicRuleCoverage Var
  denotational_semantics_respects_types : Prop
  context_agreement_matches_pdf : Prop
  interpretation_clauses_match_pdf : Prop

/-- Semantic validity is defined from the interpretation, rather than supplied
as an arbitrary relation. -/
def DomainLogicValid {Var : Type u} (I : DomainLogicInterpretation Var)
    (s : PropertySequent Var) : Prop :=
  ∀ ρ : I.Environment,
    (∀ a : PropertyAssumption Var, a ∈ s.context → I.SatisfiesAssumption ρ a) →
      I.TermSatisfiesProperty ρ s

/-- The source-facing soundness/completeness claim for a fixed denotational
interpretation. -/
def DomainLogicSoundComplete {Var : Type u} (I : DomainLogicInterpretation Var) : Prop :=
  ∀ s : PropertySequent Var,
    DomainLogicDerivation Var s ↔ DomainLogicValid I s


end Chapter7
end AbramskyJung

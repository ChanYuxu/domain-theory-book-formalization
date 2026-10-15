import Practice.DomainTheory.Chapter07.Section73.Prelocale

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 7.3: types, properties, terms, and contexts

This module follows one coherent dependency cluster inside the textbook
section. The stable public import remains
`Practice.DomainTheory.Chapter07.Section73`.
-/

universe u v

namespace AbramskyJung
namespace Chapter7

/-- Type expressions for the domain-logic language. -/
inductive TypeExpr (Var : Type u) : Type u where
  | one : TypeExpr Var
  | var : Var → TypeExpr Var
  | arr : TypeExpr Var → TypeExpr Var → TypeExpr Var
  | prod : TypeExpr Var → TypeExpr Var → TypeExpr Var
  | sum : TypeExpr Var → TypeExpr Var → TypeExpr Var
  | lift : TypeExpr Var → TypeExpr Var
  | plotkin : TypeExpr Var → TypeExpr Var
  | recTy : Var → TypeExpr Var → TypeExpr Var

/-- Legacy variable-free fragment.  It remains available for the unit-type
implementation, but source-facing closed recursive types use
`TypeExpr.IsClosed` below because `TypeExpr Empty` cannot contain a named
recursive binder. -/
abbrev ClosedTypeExpr : Type :=
  TypeExpr Empty

/-- Free variables of type expressions; `recTy` binds its variable. -/
inductive TypeExpr.FreeVar {Var : Type u} (X : Var) :
    TypeExpr Var → Prop where
  | var : TypeExpr.FreeVar X (.var X)
  | arr_left {σ τ : TypeExpr Var} :
      TypeExpr.FreeVar X σ → TypeExpr.FreeVar X (.arr σ τ)
  | arr_right {σ τ : TypeExpr Var} :
      TypeExpr.FreeVar X τ → TypeExpr.FreeVar X (.arr σ τ)
  | prod_left {σ τ : TypeExpr Var} :
      TypeExpr.FreeVar X σ → TypeExpr.FreeVar X (.prod σ τ)
  | prod_right {σ τ : TypeExpr Var} :
      TypeExpr.FreeVar X τ → TypeExpr.FreeVar X (.prod σ τ)
  | sum_left {σ τ : TypeExpr Var} :
      TypeExpr.FreeVar X σ → TypeExpr.FreeVar X (.sum σ τ)
  | sum_right {σ τ : TypeExpr Var} :
      TypeExpr.FreeVar X τ → TypeExpr.FreeVar X (.sum σ τ)
  | lift {σ : TypeExpr Var} :
      TypeExpr.FreeVar X σ → TypeExpr.FreeVar X (.lift σ)
  | plotkin {σ : TypeExpr Var} :
      TypeExpr.FreeVar X σ → TypeExpr.FreeVar X (.plotkin σ)
  | rec_body {Y : Var} {body : TypeExpr Var} :
      Y ≠ X → TypeExpr.FreeVar X body → TypeExpr.FreeVar X (.recTy Y body)

/-- A type expression is closed when it has no free type variables.  The
ambient variable type may still provide names for recursive binders. -/
def TypeExpr.IsClosed {Var : Type u} (σ : TypeExpr Var) : Prop :=
  ∀ X : Var, ¬ TypeExpr.FreeVar X σ

/-- The closed recursive type `rec 0. 0`, demonstrating that the source-facing
closed-type interface represents recursive binders. -/
def TypeExpr.closedRecursiveIdentity : TypeExpr Nat :=
  .recTy 0 (.var 0)

theorem TypeExpr.closedRecursiveIdentity_isClosed :
    TypeExpr.IsClosed TypeExpr.closedRecursiveIdentity := by
  intro X hX
  cases hX with
  | rec_body hne hbody =>
      cases hbody
      exact hne rfl

/-- Capture-aware substitution relation for type expressions.  The constructor
`rec_same` stops below a binder for the substituted variable, while `rec_other`
continues below distinct binders only when the binder is fresh for the
replacement expression. -/
inductive TypeExpr.Subst {Var : Type u} (X : Var) (replacement : TypeExpr Var) :
    TypeExpr Var → TypeExpr Var → Prop where
  | one : TypeExpr.Subst X replacement .one .one
  | var_same : TypeExpr.Subst X replacement (.var X) replacement
  | var_other {Y : Var} : Y ≠ X →
      TypeExpr.Subst X replacement (.var Y) (.var Y)
  | arr {σ τ σ' τ' : TypeExpr Var} :
      TypeExpr.Subst X replacement σ σ' →
        TypeExpr.Subst X replacement τ τ' →
          TypeExpr.Subst X replacement (.arr σ τ) (.arr σ' τ')
  | prod {σ τ σ' τ' : TypeExpr Var} :
      TypeExpr.Subst X replacement σ σ' →
        TypeExpr.Subst X replacement τ τ' →
          TypeExpr.Subst X replacement (.prod σ τ) (.prod σ' τ')
  | sum {σ τ σ' τ' : TypeExpr Var} :
      TypeExpr.Subst X replacement σ σ' →
        TypeExpr.Subst X replacement τ τ' →
          TypeExpr.Subst X replacement (.sum σ τ) (.sum σ' τ')
  | lift {σ σ' : TypeExpr Var} :
      TypeExpr.Subst X replacement σ σ' →
        TypeExpr.Subst X replacement (.lift σ) (.lift σ')
  | plotkin {σ σ' : TypeExpr Var} :
      TypeExpr.Subst X replacement σ σ' →
        TypeExpr.Subst X replacement (.plotkin σ) (.plotkin σ')
  | rec_same (body : TypeExpr Var) :
      TypeExpr.Subst X replacement (.recTy X body) (.recTy X body)
  | rec_other {Y : Var} {body body' : TypeExpr Var} :
      Y ≠ X →
        ¬ TypeExpr.FreeVar Y replacement →
        TypeExpr.Subst X replacement body body' →
          TypeExpr.Subst X replacement (.recTy Y body) (.recTy Y body')

/-- The body type of `rec X. σ`, after substituting the recursive type for `X`. -/
def TypeExpr.RecUnfolding {Var : Type u} (X : Var) (σ τ : TypeExpr Var) : Prop :=
  TypeExpr.Subst X (.recTy X σ) σ τ

/-- Properties associated with type expressions. -/
inductive PropertyExpr (Var : Type u) : TypeExpr Var → Type u where
  | truth {σ : TypeExpr Var} : PropertyExpr Var σ
  | falsity {σ : TypeExpr Var} : PropertyExpr Var σ
  | conj {σ : TypeExpr Var} :
      PropertyExpr Var σ → PropertyExpr Var σ → PropertyExpr Var σ
  | disj {σ : TypeExpr Var} :
      PropertyExpr Var σ → PropertyExpr Var σ → PropertyExpr Var σ
  | arrow {σ τ : TypeExpr Var} :
      PropertyExpr Var σ → PropertyExpr Var τ → PropertyExpr Var (.arr σ τ)
  | product {σ τ : TypeExpr Var} :
      PropertyExpr Var σ → PropertyExpr Var τ → PropertyExpr Var (.prod σ τ)
  | sumLeft {σ τ : TypeExpr Var} :
      PropertyExpr Var σ → PropertyExpr Var (.sum σ τ)
  | sumRight {σ τ : TypeExpr Var} :
      PropertyExpr Var τ → PropertyExpr Var (.sum σ τ)
  | lifted {σ : TypeExpr Var} :
      PropertyExpr Var σ → PropertyExpr Var (.lift σ)
  | box {σ : TypeExpr Var} :
      PropertyExpr Var σ → PropertyExpr Var (.plotkin σ)
  | diamond {σ : TypeExpr Var} :
      PropertyExpr Var σ → PropertyExpr Var (.plotkin σ)
  | recProp {X : Var} {σ τ : TypeExpr Var} :
      TypeExpr.RecUnfolding X σ τ →
        PropertyExpr Var τ → PropertyExpr Var (.recTy X σ)

/-- Finite disjunctions of properties, used by the decidability theorem's
normal-form package. -/
def PropertyExpr.finiteDisj {Var : Type u} {σ : TypeExpr Var} :
    List (PropertyExpr Var σ) → PropertyExpr Var σ
  | [] => PropertyExpr.falsity
  | φ :: rest => PropertyExpr.disj φ (PropertyExpr.finiteDisj rest)

/-- A structural size for property expressions.  This makes explicit the
"finitely many construction steps" used in the proof of Theorem 7.3.17. -/
def PropertyExpr.size {Var : Type u} : {σ : TypeExpr Var} → PropertyExpr Var σ → Nat
  | _, PropertyExpr.truth => 1
  | _, PropertyExpr.falsity => 1
  | _, PropertyExpr.conj φ ψ => 1 + PropertyExpr.size φ + PropertyExpr.size ψ
  | _, PropertyExpr.disj φ ψ => 1 + PropertyExpr.size φ + PropertyExpr.size ψ
  | _, PropertyExpr.arrow φ ψ => 1 + PropertyExpr.size φ + PropertyExpr.size ψ
  | _, PropertyExpr.product φ ψ => 1 + PropertyExpr.size φ + PropertyExpr.size ψ
  | _, PropertyExpr.sumLeft φ => 1 + PropertyExpr.size φ
  | _, PropertyExpr.sumRight ψ => 1 + PropertyExpr.size ψ
  | _, PropertyExpr.lifted φ => 1 + PropertyExpr.size φ
  | _, PropertyExpr.box φ => 1 + PropertyExpr.size φ
  | _, PropertyExpr.diamond φ => 1 + PropertyExpr.size φ
  | _, PropertyExpr.recProp _h φ => 1 + PropertyExpr.size φ

/-- Every property expression has a finite nonzero construction size. -/
theorem PropertyExpr.size_pos {Var : Type u} :
    ∀ {σ : TypeExpr Var}, (φ : PropertyExpr Var σ) → 0 < PropertyExpr.size φ
  | _, PropertyExpr.truth => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.falsity => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.conj φ ψ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.disj φ ψ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.arrow φ ψ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.product φ ψ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.sumLeft φ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.sumRight ψ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.lifted φ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.box φ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.diamond φ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.recProp _h φ => by
      simp [PropertyExpr.size]

/-- The distributive-lattice preorder rules displayed before Theorem 7.3.16,
recorded over the chosen carrier interpretation of formulas. -/
structure PropertyPreorderLatticeRules
    {Var : Type v} (σ : TypeExpr Var) (α : Type u) (le : α → α → Prop)
    (denote : PropertyExpr Var σ → α) : Prop where
  refl : ∀ φ : PropertyExpr Var σ, le (denote φ) (denote φ)
  trans :
    ∀ φ ψ χ : PropertyExpr Var σ,
      le (denote φ) (denote ψ) → le (denote ψ) (denote χ) →
        le (denote φ) (denote χ)
  le_true :
    ∀ φ : PropertyExpr Var σ,
      le (denote φ) (denote (PropertyExpr.truth : PropertyExpr Var σ))
  conj_intro :
    ∀ φ ψ₁ ψ₂ : PropertyExpr Var σ,
      le (denote φ) (denote ψ₁) → le (denote φ) (denote ψ₂) →
        le (denote φ) (denote (PropertyExpr.conj ψ₁ ψ₂))
  conj_left :
    ∀ φ ψ : PropertyExpr Var σ,
      le (denote (PropertyExpr.conj φ ψ)) (denote φ)
  conj_right :
    ∀ φ ψ : PropertyExpr Var σ,
      le (denote (PropertyExpr.conj φ ψ)) (denote ψ)
  false_le :
    ∀ φ : PropertyExpr Var σ,
      le (denote (PropertyExpr.falsity : PropertyExpr Var σ)) (denote φ)
  disj_elim :
    ∀ φ₁ φ₂ ψ : PropertyExpr Var σ,
      le (denote φ₁) (denote ψ) → le (denote φ₂) (denote ψ) →
        le (denote (PropertyExpr.disj φ₁ φ₂)) (denote ψ)
  le_disj_left :
    ∀ φ ψ : PropertyExpr Var σ,
      le (denote φ) (denote (PropertyExpr.disj φ ψ))
  le_disj_right :
    ∀ φ ψ : PropertyExpr Var σ,
      le (denote ψ) (denote (PropertyExpr.disj φ ψ))
  distributivity :
    ∀ φ ψ χ : PropertyExpr Var σ,
      le
        (denote (PropertyExpr.conj φ (PropertyExpr.disj ψ χ)))
        (denote
          (PropertyExpr.disj
            (PropertyExpr.conj φ ψ) (PropertyExpr.conj φ χ)))

/-- The formalized core of the syntactic domain prelocale `L(σ)` generated by
the property language of a closed type expression. It records the
formula-to-carrier interpretation and the distributive-lattice rules proved
below. The type-specific preorder rules and the inductive `C`/`T` rule systems
cited to Abramsky's thesis are intentionally not represented by dummy fields;
their construction remains part of Theorem 7.3.16's tracked interface debt. -/
structure PropertyLanguagePrelocale {Var : Type v} (σ : TypeExpr Var) where
  prelocale : DomainPrelocale.{u}
  denote : PropertyExpr Var σ → prelocale.carrier
  truth_is_one :
    RelEquiv prelocale.le
      (denote (PropertyExpr.truth : PropertyExpr Var σ)) prelocale.one
  falsity_is_zero :
    RelEquiv prelocale.le
      (denote (PropertyExpr.falsity : PropertyExpr Var σ)) prelocale.zero
  conj_is_inf :
    ∀ φ ψ : PropertyExpr Var σ,
      RelEquiv prelocale.le
        (denote (PropertyExpr.conj φ ψ)) (prelocale.inf (denote φ) (denote ψ))
  disj_is_sup :
    ∀ φ ψ : PropertyExpr Var σ,
      RelEquiv prelocale.le
        (denote (PropertyExpr.disj φ ψ)) (prelocale.sup (denote φ) (denote ψ))
  generated_by_properties :
    ∀ a : prelocale.carrier,
      ∃ φ : PropertyExpr Var σ, RelEquiv prelocale.le (denote φ) a
  preorder_lattice_rules :
    PropertyPreorderLatticeRules σ prelocale.carrier prelocale.le denote

/-- Terms associated with type expressions.  The `typedVar` constructor
represents the denumerable set `V(σ)` of point variables for each closed or open
type expression; the other constructors mirror the term grammar displayed before
Theorem 7.3.18. -/
inductive TermExpr (Var : Type u) : TypeExpr Var → Type u where
  | bottom {σ : TypeExpr Var} : TermExpr Var σ
  | typedVar {σ : TypeExpr Var} : Nat → TermExpr Var σ
  | var (x : Var) : TermExpr Var (.var x)
  | lam {σ τ : TypeExpr Var} : TermExpr Var τ → TermExpr Var (.arr σ τ)
  | app {σ τ : TypeExpr Var} :
      TermExpr Var (.arr σ τ) → TermExpr Var σ → TermExpr Var τ
  | pair {σ τ : TypeExpr Var} :
      TermExpr Var σ → TermExpr Var τ → TermExpr Var (.prod σ τ)
  | letPair {σ τ ν : TypeExpr Var} :
      TermExpr Var (.prod σ τ) → TermExpr Var ν → TermExpr Var ν
  | inl {σ τ : TypeExpr Var} : TermExpr Var σ → TermExpr Var (.sum σ τ)
  | inr {σ τ : TypeExpr Var} : TermExpr Var τ → TermExpr Var (.sum σ τ)
  | caseSum {σ τ ν : TypeExpr Var} :
      TermExpr Var (.sum σ τ) → TermExpr Var ν → TermExpr Var ν → TermExpr Var ν
  | up {σ : TypeExpr Var} : TermExpr Var σ → TermExpr Var (.lift σ)
  | liftElim {σ τ : TypeExpr Var} :
      TermExpr Var (.lift σ) → TermExpr Var τ → TermExpr Var τ
  | singleton {σ : TypeExpr Var} : TermExpr Var σ → TermExpr Var (.plotkin σ)
  | over {σ τ : TypeExpr Var} :
      TermExpr Var (.plotkin σ) → TermExpr Var (.plotkin τ) →
        TermExpr Var (.plotkin τ)
  | union {σ : TypeExpr Var} :
      TermExpr Var (.plotkin σ) → TermExpr Var (.plotkin σ) → TermExpr Var (.plotkin σ)
  | tensor {σ τ : TypeExpr Var} :
      TermExpr Var (.plotkin σ) → TermExpr Var (.plotkin τ) →
        TermExpr Var (.plotkin (.prod σ τ))
  | fold {X : Var} {σ τ : TypeExpr Var} :
      TypeExpr.RecUnfolding X σ τ →
        TermExpr Var τ → TermExpr Var (.recTy X σ)
  | unfold {X : Var} {σ τ : TypeExpr Var} :
      TypeExpr.RecUnfolding X σ τ →
        TermExpr Var (.recTy X σ) → TermExpr Var τ
  | mu {σ : TypeExpr Var} : TermExpr Var σ → TermExpr Var σ

/-- A typed assumption in the property logic. -/
structure PropertyAssumption (Var : Type u) where
  σ : TypeExpr Var
  varName : Nat
  property : PropertyExpr Var σ

/-- Contexts contain at most one assumption for each variable, as in the PDF's
side condition on finite assumption lists. -/
def PropertyContextFunctional {Var : Type u}
    (Γ : List (PropertyAssumption Var)) : Prop :=
  ∀ a b : PropertyAssumption Var,
    a ∈ Γ → b ∈ Γ → a.σ = b.σ → a.varName = b.varName → a = b

/-- Sequents `Gamma |- M : phi`. -/
structure PropertySequent (Var : Type u) where
  context : List (PropertyAssumption Var)
  context_functional : PropertyContextFunctional context
  σ : TypeExpr Var
  term : TermExpr Var σ
  property : PropertyExpr Var σ

/-- Build a sequent from a context, a term, and a property of the term's type. -/
def PropertySequent.ofTerm {Var : Type u}
    (Γ : List (PropertyAssumption Var)) (hΓ : PropertyContextFunctional Γ)
    {σ : TypeExpr Var} (M : TermExpr Var σ) (φ : PropertyExpr Var σ) :
    PropertySequent Var where
  context := Γ
  context_functional := hΓ
  σ := σ
  term := M
  property := φ

/-- Change the goal property while keeping the context and term fixed. -/
def PropertySequent.withProperty {Var : Type u}
    (s : PropertySequent Var) (φ : PropertyExpr Var s.σ) :
    PropertySequent Var where
  context := s.context
  context_functional := s.context_functional
  σ := s.σ
  term := s.term
  property := φ

/-- Change the context while keeping the typed term and property fixed. -/
def PropertySequent.withContext {Var : Type u}
    (s : PropertySequent Var)
    (Γ : List (PropertyAssumption Var)) (hΓ : PropertyContextFunctional Γ) :
    PropertySequent Var where
  context := Γ
  context_functional := hΓ
  σ := s.σ
  term := s.term
  property := s.property

/-- The formula-preorder rules used by the property-logic sequent calculus. -/
inductive PropertyFormulaPreorder (Var : Type u) :
    {σ : TypeExpr Var} → PropertyExpr Var σ → PropertyExpr Var σ → Prop where
  | refl {σ : TypeExpr Var} (φ : PropertyExpr Var σ) :
      PropertyFormulaPreorder Var φ φ
  | trans {σ : TypeExpr Var} {φ ψ χ : PropertyExpr Var σ} :
      PropertyFormulaPreorder Var φ ψ →
        PropertyFormulaPreorder Var ψ χ →
          PropertyFormulaPreorder Var φ χ
  | le_true {σ : TypeExpr Var} (φ : PropertyExpr Var σ) :
      PropertyFormulaPreorder Var φ PropertyExpr.truth
  | false_le {σ : TypeExpr Var} (φ : PropertyExpr Var σ) :
      PropertyFormulaPreorder Var PropertyExpr.falsity φ
  | conj_intro {σ : TypeExpr Var} {φ ψ χ : PropertyExpr Var σ} :
      PropertyFormulaPreorder Var φ ψ →
        PropertyFormulaPreorder Var φ χ →
          PropertyFormulaPreorder Var φ (PropertyExpr.conj ψ χ)
  | conj_left {σ : TypeExpr Var} (φ ψ : PropertyExpr Var σ) :
      PropertyFormulaPreorder Var (PropertyExpr.conj φ ψ) φ
  | conj_right {σ : TypeExpr Var} (φ ψ : PropertyExpr Var σ) :
      PropertyFormulaPreorder Var (PropertyExpr.conj φ ψ) ψ
  | disj_elim {σ : TypeExpr Var} {φ ψ χ : PropertyExpr Var σ} :
      PropertyFormulaPreorder Var φ χ →
        PropertyFormulaPreorder Var ψ χ →
          PropertyFormulaPreorder Var (PropertyExpr.disj φ ψ) χ
  | le_disj_left {σ : TypeExpr Var} (φ ψ : PropertyExpr Var σ) :
      PropertyFormulaPreorder Var φ (PropertyExpr.disj φ ψ)
  | le_disj_right {σ : TypeExpr Var} (φ ψ : PropertyExpr Var σ) :
      PropertyFormulaPreorder Var ψ (PropertyExpr.disj φ ψ)
  | distributivity {σ : TypeExpr Var} (φ ψ χ : PropertyExpr Var σ) :
      PropertyFormulaPreorder Var
        (PropertyExpr.conj φ (PropertyExpr.disj ψ χ))
        (PropertyExpr.disj (PropertyExpr.conj φ ψ) (PropertyExpr.conj φ χ))

/-- Conjunction is monotone for the generated formula preorder. -/
theorem PropertyFormulaPreorder.conj_mono {Var : Type u} {σ : TypeExpr Var}
    {φ φ' ψ ψ' : PropertyExpr Var σ}
    (hφ : PropertyFormulaPreorder Var φ φ')
    (hψ : PropertyFormulaPreorder Var ψ ψ') :
    PropertyFormulaPreorder Var
      (PropertyExpr.conj φ ψ) (PropertyExpr.conj φ' ψ') := by
  exact
    PropertyFormulaPreorder.conj_intro
      (PropertyFormulaPreorder.trans
        (PropertyFormulaPreorder.conj_left φ ψ) hφ)
      (PropertyFormulaPreorder.trans
        (PropertyFormulaPreorder.conj_right φ ψ) hψ)

/-- Disjunction is monotone for the generated formula preorder. -/
theorem PropertyFormulaPreorder.disj_mono {Var : Type u} {σ : TypeExpr Var}
    {φ φ' ψ ψ' : PropertyExpr Var σ}
    (hφ : PropertyFormulaPreorder Var φ φ')
    (hψ : PropertyFormulaPreorder Var ψ ψ') :
    PropertyFormulaPreorder Var
      (PropertyExpr.disj φ ψ) (PropertyExpr.disj φ' ψ') := by
  exact
    PropertyFormulaPreorder.disj_elim
      (PropertyFormulaPreorder.trans hφ
        (PropertyFormulaPreorder.le_disj_left φ' ψ'))
      (PropertyFormulaPreorder.trans hψ
        (PropertyFormulaPreorder.le_disj_right φ' ψ'))

/-- Conjunction is commutative up to the generated formula preorder. -/
theorem PropertyFormulaPreorder.conj_comm {Var : Type u} {σ : TypeExpr Var}
    (φ ψ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.conj φ ψ) (PropertyExpr.conj ψ φ) := by
  exact
    PropertyFormulaPreorder.conj_intro
      (PropertyFormulaPreorder.conj_right φ ψ)
      (PropertyFormulaPreorder.conj_left φ ψ)

/-- Disjunction is commutative up to the generated formula preorder. -/
theorem PropertyFormulaPreorder.disj_comm {Var : Type u} {σ : TypeExpr Var}
    (φ ψ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.disj φ ψ) (PropertyExpr.disj ψ φ) := by
  exact
    PropertyFormulaPreorder.disj_elim
      (PropertyFormulaPreorder.le_disj_right ψ φ)
      (PropertyFormulaPreorder.le_disj_left ψ φ)

/-- Every listed formula is below its finite disjunction. -/
theorem PropertyFormulaPreorder.le_finiteDisj_of_mem {Var : Type u}
    {σ : TypeExpr Var} {φ : PropertyExpr Var σ} {l : List (PropertyExpr Var σ)}
    (hmem : φ ∈ l) :
    PropertyFormulaPreorder Var φ (PropertyExpr.finiteDisj l) := by
  induction l with
  | nil =>
      cases hmem
  | cons head rest ih =>
      simp only [List.mem_cons] at hmem
      change
        PropertyFormulaPreorder Var φ
          (PropertyExpr.disj head (PropertyExpr.finiteDisj rest))
      rcases hmem with hφ | hmem
      · cases hφ
        exact PropertyFormulaPreorder.le_disj_left φ (PropertyExpr.finiteDisj rest)
      · exact
          PropertyFormulaPreorder.trans (ih hmem)
            (PropertyFormulaPreorder.le_disj_right head (PropertyExpr.finiteDisj rest))

/-- A finite disjunction is below a formula if every listed disjunct is below it. -/
theorem PropertyFormulaPreorder.finiteDisj_le {Var : Type u}
    {σ : TypeExpr Var} {l : List (PropertyExpr Var σ)} {ψ : PropertyExpr Var σ}
    (h : ∀ φ : PropertyExpr Var σ, φ ∈ l → PropertyFormulaPreorder Var φ ψ) :
    PropertyFormulaPreorder Var (PropertyExpr.finiteDisj l) ψ := by
  induction l with
  | nil =>
      exact PropertyFormulaPreorder.false_le ψ
  | cons φ rest ih =>
      simp only [PropertyExpr.finiteDisj]
      refine PropertyFormulaPreorder.disj_elim (h φ ?_) ?_
      · simp
      · exact ih (by
          intro χ hχ
          exact h χ (by simp [hχ]))

/-- Formula filters over a fixed type in the property-language preorder. -/
structure PropertyFormulaFilter (Var : Type u) {σ : TypeExpr Var}
    (F : Set (PropertyExpr Var σ)) : Prop where
  truth_mem : (PropertyExpr.truth : PropertyExpr Var σ) ∈ F
  upward_closed :
    ∀ ⦃φ ψ : PropertyExpr Var σ⦄,
      φ ∈ F → PropertyFormulaPreorder Var φ ψ → ψ ∈ F
  conj_closed :
    ∀ ⦃φ ψ : PropertyExpr Var σ⦄,
      φ ∈ F → ψ ∈ F → PropertyExpr.conj φ ψ ∈ F

/-- Prime formula filters add properness and disjunction primality. -/
structure PropertyFormulaPrimeFilter (Var : Type u) {σ : TypeExpr Var}
    (F : Set (PropertyExpr Var σ)) : Prop
    extends PropertyFormulaFilter Var F where
  false_not_mem : (PropertyExpr.falsity : PropertyExpr Var σ) ∉ F
  disj_prime :
    ∀ ⦃φ ψ : PropertyExpr Var σ⦄,
      PropertyExpr.disj φ ψ ∈ F → φ ∈ F ∨ ψ ∈ F

/-- A property assumption is prime when its formula is join-prime in the
formula preorder for its type. -/
def PropertyAssumption.IsPrime {Var : Type u} (a : PropertyAssumption Var) :
    Prop :=
  ∀ ψ χ : PropertyExpr Var a.σ,
    PropertyFormulaPreorder Var a.property (PropertyExpr.disj ψ χ) →
      PropertyFormulaPreorder Var a.property ψ ∨
        PropertyFormulaPreorder Var a.property χ

/-- Prime contexts satisfy the finite-context functionality side condition and
carry only prime property assumptions. -/
def PropertyContextPrime {Var : Type u}
    (Γ : List (PropertyAssumption Var)) : Prop :=
  PropertyContextFunctional Γ ∧
    ∀ a : PropertyAssumption Var, a ∈ Γ → a.IsPrime

/-- Formula filters contain a conjunction exactly when they contain both
conjuncts. -/
theorem PropertyFormulaFilter.conj_mem_iff {Var : Type u} {σ : TypeExpr Var}
    {F : Set (PropertyExpr Var σ)} (hF : PropertyFormulaFilter Var F)
    (φ ψ : PropertyExpr Var σ) :
    PropertyExpr.conj φ ψ ∈ F ↔ φ ∈ F ∧ ψ ∈ F := by
  constructor
  · intro h
    exact
      ⟨hF.upward_closed h (PropertyFormulaPreorder.conj_left φ ψ),
        hF.upward_closed h (PropertyFormulaPreorder.conj_right φ ψ)⟩
  · intro h
    exact hF.conj_closed h.1 h.2

/-- A formula filter contains a finite disjunction whenever it contains one of
the listed disjuncts. -/
theorem PropertyFormulaFilter.finiteDisj_mem_of_mem {Var : Type u}
    {σ : TypeExpr Var} {F : Set (PropertyExpr Var σ)}
    (hF : PropertyFormulaFilter Var F)
    {l : List (PropertyExpr Var σ)} {φ : PropertyExpr Var σ}
    (hmem : φ ∈ l) (hφ : φ ∈ F) :
    PropertyExpr.finiteDisj l ∈ F :=
  hF.upward_closed hφ (PropertyFormulaPreorder.le_finiteDisj_of_mem hmem)

/-- Prime formula filters contain a disjunction exactly when they contain one of
the disjuncts. -/
theorem PropertyFormulaPrimeFilter.disj_mem_iff {Var : Type u} {σ : TypeExpr Var}
    {F : Set (PropertyExpr Var σ)} (hF : PropertyFormulaPrimeFilter Var F)
    (φ ψ : PropertyExpr Var σ) :
    PropertyExpr.disj φ ψ ∈ F ↔ φ ∈ F ∨ ψ ∈ F := by
  constructor
  · intro h
    exact hF.disj_prime h
  · intro h
    rcases h with hφ | hψ
    · exact hF.upward_closed hφ (PropertyFormulaPreorder.le_disj_left φ ψ)
    · exact hF.upward_closed hψ (PropertyFormulaPreorder.le_disj_right φ ψ)

/-- Prime formula filters contain a finite disjunction exactly when they contain
one of the listed disjuncts. -/
theorem PropertyFormulaPrimeFilter.finiteDisj_mem_iff {Var : Type u}
    {σ : TypeExpr Var} {F : Set (PropertyExpr Var σ)}
    (hF : PropertyFormulaPrimeFilter Var F)
    (l : List (PropertyExpr Var σ)) :
    PropertyExpr.finiteDisj l ∈ F ↔ ∃ φ : PropertyExpr Var σ, φ ∈ l ∧ φ ∈ F := by
  induction l with
  | nil =>
      constructor
      · intro h
        exact False.elim (hF.false_not_mem h)
      · intro h
        rcases h with ⟨φ, hmem, _hφ⟩
        cases hmem
  | cons φ rest ih =>
      constructor
      · intro h
        have hdisj :
            PropertyExpr.disj φ (PropertyExpr.finiteDisj rest) ∈ F := by
          simpa [PropertyExpr.finiteDisj] using h
        rcases (PropertyFormulaPrimeFilter.disj_mem_iff hF φ
            (PropertyExpr.finiteDisj rest)).1 hdisj with hφ | hrest
        · exact ⟨φ, by simp, hφ⟩
        · rcases ih.1 hrest with ⟨ψ, hψmem, hψ⟩
          exact ⟨ψ, by simp [hψmem], hψ⟩
      · intro h
        rcases h with ⟨ψ, hψmem, hψ⟩
        exact
          hF.toPropertyFormulaFilter.finiteDisj_mem_of_mem
            (by simpa using hψmem) hψ

/-- Prime contexts are functional contexts. -/
theorem PropertyContextPrime.functional {Var : Type u}
    {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextPrime Γ) :
    PropertyContextFunctional Γ :=
  hΓ.1

/-- Every assumption in a prime context has a prime formula. -/
theorem PropertyContextPrime.assumption_prime {Var : Type u}
    {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextPrime Γ)
    {a : PropertyAssumption Var} (ha : a ∈ Γ) :
    a.IsPrime :=
  hΓ.2 a ha

/-- The empty context is functional. -/
theorem PropertyContextFunctional.nil {Var : Type u} :
    PropertyContextFunctional ([] : List (PropertyAssumption Var)) := by
  intro a _b ha _hb _hσ _hvar
  cases ha

/-- Functionality is inherited by subcontexts. -/
theorem PropertyContextFunctional.subset {Var : Type u}
    {Γ Δ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
    (hsub : ∀ a : PropertyAssumption Var, a ∈ Δ → a ∈ Γ) :
    PropertyContextFunctional Δ := by
  intro a b ha hb hσ hvar
  exact hΓ a b (hsub a ha) (hsub b hb) hσ hvar

/-- A fresh assumption can be consed onto a functional context. -/
theorem PropertyContextFunctional.cons {Var : Type u}
    {Γ : List (PropertyAssumption Var)} {a : PropertyAssumption Var}
    (hΓ : PropertyContextFunctional Γ)
    (hfresh :
      ∀ b : PropertyAssumption Var, b ∈ Γ →
        a.σ = b.σ → a.varName = b.varName → False) :
    PropertyContextFunctional (a :: Γ) := by
  intro x y hx hy hσ hvar
  simp only [List.mem_cons] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · rfl
    · exact False.elim (hfresh y hy hσ hvar)
  · rcases hy with rfl | hy
    · exact False.elim (hfresh x hx hσ.symm hvar.symm)
    · exact hΓ x y hx hy hσ hvar

/-- The empty context is prime. -/
theorem PropertyContextPrime.nil {Var : Type u} :
    PropertyContextPrime ([] : List (PropertyAssumption Var)) := by
  constructor
  · exact PropertyContextFunctional.nil
  · intro a ha
    cases ha

/-- Primality is inherited by subcontexts. -/
theorem PropertyContextPrime.subset {Var : Type u}
    {Γ Δ : List (PropertyAssumption Var)} (hΓ : PropertyContextPrime Γ)
    (hsub : ∀ a : PropertyAssumption Var, a ∈ Δ → a ∈ Γ) :
    PropertyContextPrime Δ := by
  constructor
  · exact PropertyContextFunctional.subset hΓ.1 hsub
  · intro a ha
    exact hΓ.2 a (hsub a ha)

/-- A fresh prime assumption can be consed onto a prime context. -/
theorem PropertyContextPrime.cons {Var : Type u}
    {Γ : List (PropertyAssumption Var)} {a : PropertyAssumption Var}
    (hΓ : PropertyContextPrime Γ) (ha : a.IsPrime)
    (hfresh :
      ∀ b : PropertyAssumption Var, b ∈ Γ →
        a.σ = b.σ → a.varName = b.varName → False) :
    PropertyContextPrime (a :: Γ) := by
  constructor
  · exact PropertyContextFunctional.cons hΓ.1 hfresh
  · intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ha
    · exact hΓ.2 b hb

/-- The tail of a functional cons context is functional. -/
theorem PropertyContextFunctional.tail {Var : Type u}
    {Γ : List (PropertyAssumption Var)} {a : PropertyAssumption Var}
    (hΓ : PropertyContextFunctional (a :: Γ)) :
    PropertyContextFunctional Γ := by
  exact
    PropertyContextFunctional.subset hΓ
      (by
        intro b hb
        simp [hb])

/-- In a functional cons context, a tail assumption with the head variable is
equal to the head assumption. -/
theorem PropertyContextFunctional.head_eq_of_same_var {Var : Type u}
    {Γ : List (PropertyAssumption Var)} {a b : PropertyAssumption Var}
    (hΓ : PropertyContextFunctional (a :: Γ)) (hb : b ∈ Γ)
    (hσ : a.σ = b.σ) (hvar : a.varName = b.varName) :
    a = b := by
  exact hΓ a b (by simp) (by simp [hb]) hσ hvar

/-- The head assumption of a prime cons context is prime. -/
theorem PropertyContextPrime.head_prime {Var : Type u}
    {Γ : List (PropertyAssumption Var)} {a : PropertyAssumption Var}
    (hΓ : PropertyContextPrime (a :: Γ)) :
    a.IsPrime := by
  exact hΓ.2 a (by simp)

/-- The tail of a prime cons context is prime. -/
theorem PropertyContextPrime.tail {Var : Type u}
    {Γ : List (PropertyAssumption Var)} {a : PropertyAssumption Var}
    (hΓ : PropertyContextPrime (a :: Γ)) :
    PropertyContextPrime Γ := by
  exact
    PropertyContextPrime.subset hΓ
      (by
        intro b hb
        simp [hb])

/-- In a prime cons context, a tail assumption with the head variable is equal
to the head assumption. -/
theorem PropertyContextPrime.head_eq_of_same_var {Var : Type u}
    {Γ : List (PropertyAssumption Var)} {a b : PropertyAssumption Var}
    (hΓ : PropertyContextPrime (a :: Γ)) (hb : b ∈ Γ)
    (hσ : a.σ = b.σ) (hvar : a.varName = b.varName) :
    a = b := by
  exact PropertyContextFunctional.head_eq_of_same_var hΓ.1 hb hσ hvar

end Chapter7
end AbramskyJung

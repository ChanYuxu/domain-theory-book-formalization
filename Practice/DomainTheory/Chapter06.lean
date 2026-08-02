import Practice.DomainTheory.Chapter05

set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-!
# Abramsky--Jung, Domain Theory, Chapter 6

This chapter formalizes signatures, terms, inequational theories, free
domain-algebras, strict algebras, and the named powerdomain constructions.

Numbered declarations live in `Chapter06/Section61.lean` and
`Chapter06/Section62.lean`, with `Chapter06/NumberedItems.lean` as the
aggregator.  Several high-level existence and representation theorems are
currently represented by explicit principle interfaces or lightweight witnesses;
the semantic-strength audit is tracked in `formalization_status.md`.
-/

universe u v w

namespace AbramskyJung
namespace Chapter6

open Chapter4

/-- A finitary operation signature with an arity type for each operation.  The
PDF writes this as a map `alpha : Omega -> Nat`; the Lean version keeps the
arity as a finite type. -/
structure Signature where
  Op : Type u
  arity : Op → Type v
  arity_finite : ∀ o : Op, Finite (arity o)

/-- Terms over a signature and a type of variables. -/
inductive Term (Sig : Signature.{u, v}) (Var : Type w) :
    Type (max u v w) where
  | var : Var → Term Sig Var
  | op : (o : Sig.Op) → (Sig.arity o → Term Sig Var) → Term Sig Var

/-- An algebra for a signature on an ordered domain.  The dcpo and continuity
requirements for dcpo-algebras are recorded by `Model`. -/
structure Algebra (Sig : Signature.{u, v}) (D : OrderedDomain.{w}) where
  op : ∀ o : Sig.Op, (Sig.arity o → D.carrier) → D.carrier

namespace Term

/-- Evaluation of terms in an algebra under a variable assignment. -/
def eval {Sig : Signature.{u, v}} {Var : Type w} {D : OrderedDomain.{w}}
    (A : Algebra Sig D) (ρ : Var → D.carrier) :
    Term Sig Var → D.carrier
  | var x => ρ x
  | op o args => A.op o (fun i => eval A ρ (args i))

end Term

/-- An inequation between two terms over the same variables. -/
structure Inequation (Sig : Signature.{u, v}) (Var : Type w) where
  lhs : Term Sig Var
  rhs : Term Sig Var

/-- Satisfaction of an inequation by an ordered algebra. -/
def Algebra.Satisfies {Sig : Signature.{u, v}} {Var : Type w}
    {D : OrderedDomain.{w}} (A : Algebra Sig D) (e : Inequation Sig Var) : Prop :=
  ∀ ρ : Var → D.carrier, Term.eval A ρ e.lhs ≤ Term.eval A ρ e.rhs

/-- An inequational theory over a fixed variable type. -/
structure Theory (Sig : Signature.{u, v}) (Var : Type w) where
  inequations : Set (Inequation Sig Var)

/-- A dcpo-algebra model of an inequational theory. -/
structure Model {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) where
  domain : OrderedDomain.{w}
  dcpo : Chapter3.IsDcpo domain.carrier
  algebra : Algebra Sig domain
  operations_scott_continuous :
    ∀ o : Sig.Op,
      Chapter3.ScottContinuous
        (fun args : Sig.arity o → domain.carrier => algebra.op o args)
  sound : ∀ e ∈ T.inequations, algebra.Satisfies e

/-- Candidate mapping data for a free dcpo-algebra.  The numbered Section 6.1
interface `FreeDcpoAlgebraForTheory` carries the actual unit, extension, and
uniqueness laws used for the PDF free-algebra statements. -/
structure FreeDcpoAlgebra (Sig : Signature.{u, v}) (X : Type w) where
  domain : OrderedDomain.{w}
  algebra : Algebra Sig domain
  unit : X → domain.carrier
  lift :
    ∀ (M : OrderedDomain.{w}) (_A : Algebra Sig M),
      (X → M.carrier) → OrderedDomain.ContFunCarrier domain M

/-- Auxiliary stricter algebra interface whose operations preserve bottom.  This
is stronger than numbered Definition 6.1.12, where strictness only refers to a
least element in the carrier and bottom-preserving homomorphisms. -/
structure StrictAlgebra (Sig : Signature.{u, v}) extends OrderedDomain.{w} where
  bottom : carrier
  bottom_le : ∀ x : carrier, bottom ≤ x
  algebra : Algebra Sig toOrderedDomain
  strict :
    ∀ o : Sig.Op, algebra.op o (fun _ => bottom) = bottom

/-- The powerdomain constructions named in Chapter 6. -/
inductive PowerdomainKind where
  | plotkin
  | hoare
  | smyth
  | probabilistic
deriving DecidableEq, Repr

/-- A generic interface for a powerdomain over `D`. -/
structure Powerdomain (D : OrderedDomain.{u}) where
  kind : PowerdomainKind
  carrier : OrderedDomain.{u}
  unit : OrderedDomain.ContFunCarrier D carrier
  unionLike : carrier.carrier → carrier.carrier → carrier.carrier

/-- The topological representation data for a powerdomain. -/
structure PowerdomainRepresentation (D : OrderedDomain.{u}) where
  powerdomain : Powerdomain D
  represented_subsets : Set (Set D.carrier)
  encode : powerdomain.carrier.carrier → represented_subsets
  decode : represented_subsets → powerdomain.carrier.carrier
  encode_decode : ∀ x : represented_subsets, encode (decode x) = x
  decode_encode : ∀ x : powerdomain.carrier.carrier, decode (encode x) = x

end Chapter6
end AbramskyJung

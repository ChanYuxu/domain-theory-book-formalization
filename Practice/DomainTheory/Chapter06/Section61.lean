import Practice.DomainTheory.Chapter06

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Chapter 6.1: free dcpo-algebras and strict algebras

This section records the numbered Section 6.1 items over the bundled
order/domain APIs.  Several existence theorems are registered as visible proof
debt with auxiliary packages rather than the full adjoint-functor and
syntactic-basis constructions from the PDF.
-/

universe u v w z

namespace AbramskyJung
namespace Chapter6

open Chapter4

/-- A homomorphism between models of the same inequational theory. -/
structure DcpoAlgebraHom {Sig : Signature.{u, v}} {Var : Type w}
    {T : Theory Sig Var} (A B : Model T) where
  toFun : A.domain.carrier → B.domain.carrier
  continuous : Chapter3.ScottContinuous toFun
  preserves_op :
    ∀ (o : Sig.Op) (args : Sig.arity o → A.domain.carrier),
      toFun (A.algebra.op o args) = B.algebra.op o (fun i => toFun (args i))

namespace DcpoAlgebraHom

/-- The Scott-continuous function underlying a dcpo-algebra homomorphism. -/
def toContFun {Sig : Signature.{u, v}} {Var : Type w} {T : Theory Sig Var}
    {A B : Model T} (h : DcpoAlgebraHom A B) :
    OrderedDomain.ContFunCarrier A.domain B.domain where
  toFun := h.toFun
  continuous := h.continuous

end DcpoAlgebraHom

/-- Product data in the category of dcpo-algebras of an inequational theory. -/
structure DcpoAlgebraProduct {Sig : Signature.{u, v}} {Var : Type w}
    {T : Theory Sig Var} (I : Type w) (A : I → Model T) where
  object : Model T
  projection : ∀ i : I, DcpoAlgebraHom object (A i)
  lift : ∀ B : Model T, (∀ i : I, DcpoAlgebraHom B (A i)) → DcpoAlgebraHom B object
  lift_projection :
    ∀ (B : Model T) (cone : ∀ i : I, DcpoAlgebraHom B (A i))
      (i : I) (x : B.domain.carrier),
      (projection i).toFun ((lift B cone).toFun x) = (cone i).toFun x
  lift_unique :
    ∀ (B : Model T) (cone : ∀ i : I, DcpoAlgebraHom B (A i))
      (h : DcpoAlgebraHom B object),
      (∀ i : I, ∀ x : B.domain.carrier,
        (projection i).toFun (h.toFun x) = (cone i).toFun x) →
        h = lift B cone

/-- Equalizer data in the category of dcpo-algebras of an inequational theory. -/
structure DcpoAlgebraEqualizer {Sig : Signature.{u, v}} {Var : Type w}
    {T : Theory Sig Var} {A B : Model T}
    (f g : DcpoAlgebraHom A B) where
  object : Model T
  inclusion : DcpoAlgebraHom object A
  equalizes :
    ∀ x : object.domain.carrier,
      f.toFun (inclusion.toFun x) = g.toFun (inclusion.toFun x)
  lift :
    ∀ E : Model T, (h : DcpoAlgebraHom E A) →
      (∀ x : E.domain.carrier, f.toFun (h.toFun x) = g.toFun (h.toFun x)) →
        DcpoAlgebraHom E object
  lift_inclusion :
    ∀ (E : Model T) (h : DcpoAlgebraHom E A)
      (heq : ∀ x : E.domain.carrier, f.toFun (h.toFun x) = g.toFun (h.toFun x))
      (x : E.domain.carrier),
      inclusion.toFun ((lift E h heq).toFun x) = h.toFun x
  lift_unique :
    ∀ (E : Model T) (h : DcpoAlgebraHom E A)
      (heq : ∀ x : E.domain.carrier, f.toFun (h.toFun x) = g.toFun (h.toFun x))
      (k : DcpoAlgebraHom E object),
      (∀ x : E.domain.carrier, inclusion.toFun (k.toFun x) = h.toFun x) →
        k = lift E h heq

/-- Completeness data for the category of dcpo-algebras of an inequational theory. -/
structure CompleteDcpoAlgebraCategory {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) where
  products : ∀ I : Type w, (A : I → Model T) → Nonempty (DcpoAlgebraProduct I A)
  equalizers :
    ∀ (A B : Model T), (f g : DcpoAlgebraHom A B) →
      Nonempty (DcpoAlgebraEqualizer f g)

/-- The one-point model, kept as a small model-existence sanity witness.  It is
not used as product/equalizer evidence for Proposition 6.1.1. -/
def punitModel {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) : Model T where
  domain := {
    carrier := PUnit
    preorder := inferInstance
  }
  dcpo := by
    intro A _hA
    refine ⟨PUnit.unit, ?_⟩
    constructor
    · intro a _ha
      cases a
      exact le_rfl
    · intro y _hy
      cases y
      exact le_rfl
  algebra := {
    op := fun _ _ => PUnit.unit
  }
  operations_scott_continuous := by
    intro _o
    constructor
    · intro _x _y _hxy
      exact le_rfl
    · intro _A _x _hA _hx
      constructor
      · intro y _hy
        cases y
        exact le_rfl
      · intro y _hy
        cases y
        exact le_rfl
  sound := by
    intro e _he ρ
    cases Term.eval { op := fun _ _ => PUnit.unit } ρ e.lhs
    cases Term.eval { op := fun _ _ => PUnit.unit } ρ e.rhs
    exact le_rfl

/-- Proposition 6.1.1.  PDF text: `DCPO(Σ,E)` with Scott-continuous
homomorphisms is a complete category.

The current file represents completeness by product and equalizer universal
properties; the existence proof is registered as local proof debt. -/
theorem prop_6_1_1_dcpo_algebras_complete
    {Sig : Signature.{u, v}} {Var : Type w} (T : Theory Sig Var) :
    Nonempty (CompleteDcpoAlgebraCategory T) := by
  admit

/-- Universal mapping data for a free dcpo-algebra over a dcpo. -/
structure FreeDcpoAlgebraForTheory {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) (D : OrderedDomain.{w}) where
  source_dcpo : Chapter3.IsDcpo D.carrier
  model : Model T
  unit : OrderedDomain.ContFunCarrier D model.domain
  extension :
    ∀ A : Model T,
      OrderedDomain.ContFunCarrier D A.domain → DcpoAlgebraHom model A
  extension_unit :
    ∀ (A : Model T) (g : OrderedDomain.ContFunCarrier D A.domain)
      (x : D.carrier), (extension A g).toFun (unit x) = g x
  extension_unique :
    ∀ (A : Model T) (g : OrderedDomain.ContFunCarrier D A.domain)
      (h : DcpoAlgebraHom model A),
      (∀ x : D.carrier, h.toFun (unit x) = g x) → h = extension A g

/-- Theorem 6.1.2.  PDF text: for every signature and inequational theory, the
forgetful functor `DCPO(Σ,E) -> DCPO` has a left adjoint.

The free-algebra existence construction is not yet formalized in Lean, so this
PDF-facing declaration is registered as local proof debt. -/
theorem theorem_6_1_2_free_dcpo_algebras_exist
    {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) (D : OrderedDomain.{w})
    (hDdcpo : Chapter3.IsDcpo D.carrier) :
    Nonempty (FreeDcpoAlgebraForTheory T D) := by
  admit

/-- The abstract-basis interpolation property for an arbitrary relation. -/
def IsAbstractBasisRelation {α : Type u} (r : α → α → Prop) : Prop :=
  (∀ ⦃x y z : α⦄, r x y → r y z → r x z) ∧
    ∀ x : α, ∀ M : Set α, M.Finite →
      (∀ m ∈ M, r m x) →
        ∃ y : α, (∀ m ∈ M, r m y) ∧ r y x

/-- The source basis hypothesis used in the syntactic construction: the
way-below relation on constants is already an abstract basis relation. -/
def IsSyntacticSourceBasis (B : Type w) [Preorder B] : Prop :=
  IsAbstractBasisRelation (fun x y : B => Chapter3.WayBelow x y)

/-- Relational inclusion. -/
def RelIncluded {α : Type u} (r s : α → α → Prop) : Prop :=
  ∀ ⦃x y : α⦄, r x y → s x y

/-- Relational composition, written in diagram order. -/
def RelComp {α : Type u} (r s : α → α → Prop) : α → α → Prop :=
  fun x z => ∃ y : α, r x y ∧ s y z

/-- Iterated relational composition. -/
def RelIter {α : Type u} : Nat → (α → α → Prop) → α → α → Prop
  | 0, _ => Eq
  | n + 1, r => RelComp r (RelIter n r)

/-- A local transitive closure used to model the generated approximation relation. -/
inductive RelTransGen {α : Type u} (r : α → α → Prop) : α → α → Prop where
  | single {x y : α} : r x y → RelTransGen r x y
  | tail {x y z : α} : RelTransGen r x y → r y z → RelTransGen r x z

/-- The structural approximation `≺s` on terms: terms have the same operation
shape, and corresponding constants are related by way-below. -/
inductive StrictSyntacticApprox {Sig : Signature.{u, v}} {B : Type w}
    [Preorder B] : Term Sig B → Term Sig B → Prop where
  | var {a b : B} :
      Chapter3.WayBelow a b →
        StrictSyntacticApprox (Term.var a) (Term.var b)
  | op {o : Sig.Op} {s t : Sig.arity o → Term Sig B} :
      (∀ i : Sig.arity o, StrictSyntacticApprox (s i) (t i)) →
        StrictSyntacticApprox (Term.op o s) (Term.op o t)

/-- Inequational preorder data on the term algebra over a basis.  The final
field records the derivation-replacement compatibility used in the PDF proof of
Proposition 6.1.4. -/
structure SyntacticBasisData (Sig : Signature.{u, v}) (B : Type w)
    [Preorder B] where
  source_basis : IsSyntacticSourceBasis B
  inequationalLe : Term Sig B → Term Sig B → Prop
  inequational_refl : ∀ t : Term Sig B, inequationalLe t t
  inequational_trans :
    ∀ ⦃r s t : Term Sig B⦄,
      inequationalLe r s → inequationalLe s t → inequationalLe r t
  compatible_op :
    ∀ (o : Sig.Op) (s t : Sig.arity o → Term Sig B),
      (∀ i : Sig.arity o, inequationalLe (s i) (t i)) →
        inequationalLe (Term.op o s) (Term.op o t)
  strict_inequational_interpolation :
    ∀ ⦃s t u : Term Sig B⦄,
      StrictSyntacticApprox s t →
        inequationalLe t u →
          ∃ t' u' : Term Sig B,
            StrictSyntacticApprox s t' ∧
              inequationalLe t' u' ∧ StrictSyntacticApprox u' u

/-- One generating step for the combined syntactic approximation `≺`. -/
def InequationalApproxGenerator {Sig : Signature.{u, v}} {B : Type w}
    [Preorder B] (data : SyntacticBasisData Sig B) :
    Term Sig B → Term Sig B → Prop :=
  RelComp data.inequationalLe
    (RelComp (StrictSyntacticApprox (Sig := Sig) (B := B)) data.inequationalLe)

/-- The generated approximation relation `≺` on terms. -/
def CombinedSyntacticApprox {Sig : Signature.{u, v}} {B : Type w}
    [Preorder B] (data : SyntacticBasisData Sig B) :
    Term Sig B → Term Sig B → Prop :=
  RelTransGen (InequationalApproxGenerator data)

/-- The local transitive closure is transitive. -/
theorem relTransGen_trans {α : Type u} {r : α → α → Prop}
    {x y z : α} :
    RelTransGen r x y → RelTransGen r y z → RelTransGen r x z := by
  intro hxy hyz
  induction hyz with
  | single hyz =>
      exact RelTransGen.tail hxy hyz
  | tail hyw hwz ih =>
      exact RelTransGen.tail ih hwz

/-- A single generator step embeds into the generated approximation relation. -/
theorem combinedSyntacticApprox_of_generator
    {Sig : Signature.{u, v}} {B : Type w} [Preorder B]
    {data : SyntacticBasisData Sig B} {x y : Term Sig B} :
    InequationalApproxGenerator data x y →
      CombinedSyntacticApprox data x y :=
  RelTransGen.single

/-- The generated syntactic approximation relation is transitive. -/
theorem combinedSyntacticApprox_trans
    {Sig : Signature.{u, v}} {B : Type w} [Preorder B]
    {data : SyntacticBasisData Sig B} {x y z : Term Sig B} :
    CombinedSyntacticApprox data x y →
      CombinedSyntacticApprox data y z →
        CombinedSyntacticApprox data x z :=
  relTransGen_trans

/-- Positive-length exact iterates embed in the local transitive closure. -/
theorem relIter_succ_subset_relTransGen {α : Type u} {r : α → α → Prop} :
    ∀ n : Nat, RelIncluded (RelIter (n + 1) r) (RelTransGen r) := by
  intro n
  induction n with
  | zero =>
      intro x z hxz
      rcases hxz with ⟨y, hxy, hyz⟩
      cases hyz
      exact RelTransGen.single hxy
  | succ n ih =>
      intro x z hxz
      rcases hxz with ⟨y, hxy, hyz⟩
      exact relTransGen_trans (RelTransGen.single hxy) (ih hyz)

/-- Positive-length exact iterates of the generator embed in `≺`. -/
theorem combinedSyntacticApprox_of_relIter_succ
    {Sig : Signature.{u, v}} {B : Type w} [Preorder B]
    {data : SyntacticBasisData Sig B} :
    ∀ n : Nat,
      RelIncluded
        (RelIter (n + 1) (InequationalApproxGenerator data))
        (CombinedSyntacticApprox data) :=
  relIter_succ_subset_relTransGen

/-- If a relation can split each single step into two steps, then each positive
exact iterate embeds into the next exact iterate. -/
theorem relIter_succ_subset_succ_succ_of_one_step_split
    {α : Type u} {r : α → α → Prop}
    (hsplit : RelIncluded (RelIter 1 r) (RelIter 2 r)) :
    ∀ n : Nat, RelIncluded (RelIter (n + 1) r) (RelIter (n + 2) r) := by
  intro n
  induction n with
  | zero =>
      exact hsplit
  | succ n ih =>
      intro x z hxz
      rcases hxz with ⟨y, hxy, hyz⟩
      exact ⟨y, hxy, ih hyz⟩

/-- Positive exact iterates are monotone under a one-step splitting property. -/
theorem relIter_positive_mono_of_one_step_split
    {α : Type u} {r : α → α → Prop}
    (hsplit : RelIncluded (RelIter 1 r) (RelIter 2 r)) :
    ∀ ⦃n m : Nat⦄, n ≤ m →
      RelIncluded (RelIter (n + 1) r) (RelIter (m + 1) r) := by
  intro n m hnm
  induction hnm with
  | refl =>
      intro x y hxy
      exact hxy
  | @step m _ ih =>
      intro x y hxy
      exact
        relIter_succ_subset_succ_succ_of_one_step_split hsplit m (ih hxy)

/-- Proposition 6.1.4 support, part (1): strict approximation followed by the
inequational preorder splits through another strict approximation. -/
theorem strictSyntacticApprox_comp_inequationalLe_subset
    {Sig : Signature.{u, v}} {B : Type w} [Preorder B]
    (data : SyntacticBasisData Sig B) :
    RelIncluded
        (RelComp (StrictSyntacticApprox (Sig := Sig) (B := B))
          data.inequationalLe)
        (RelComp (StrictSyntacticApprox (Sig := Sig) (B := B))
          (RelComp data.inequationalLe
            (StrictSyntacticApprox (Sig := Sig) (B := B)))) := by
  intro s u hsu
  rcases hsu with ⟨t, hst, htu⟩
  rcases data.strict_inequational_interpolation hst htu with
    ⟨t', u', hst', ht'u', hu'u⟩
  exact ⟨t', hst', ⟨u', ht'u', hu'u⟩⟩

/-- A generator step can be split into two generator steps. -/
theorem inequationalApproxGenerator_step_split
    {Sig : Signature.{u, v}} {B : Type w} [Preorder B]
    (data : SyntacticBasisData Sig B) :
    RelIncluded
      (InequationalApproxGenerator data)
      (RelIter 2 (InequationalApproxGenerator data)) := by
  intro x z hxz
  rcases hxz with ⟨t, hxt, htail⟩
  rcases htail with ⟨u, htu, huz⟩
  rcases data.strict_inequational_interpolation htu huz with
    ⟨t', u', htt', ht'u', hu'z⟩
  refine ⟨u', ?_, ?_⟩
  · exact ⟨t, hxt, ⟨t', htt', ht'u'⟩⟩
  · exact
      ⟨z, ⟨u', data.inequational_refl u',
        ⟨z, hu'z, data.inequational_refl z⟩⟩, rfl⟩

/-- A one-step generator iterate can be split into a two-step generator iterate. -/
theorem inequationalApproxGenerator_one_step_split
    {Sig : Signature.{u, v}} {B : Type w} [Preorder B]
    (data : SyntacticBasisData Sig B) :
    RelIncluded
      (RelIter 1 (InequationalApproxGenerator data))
      (RelIter 2 (InequationalApproxGenerator data)) := by
  intro x z hxz
  rcases hxz with ⟨y, hxy, hyz⟩
  cases hyz
  exact inequationalApproxGenerator_step_split data hxy

/-- The strict syntactic approximation relation inherits transitivity from the
source basis relation. -/
theorem strictSyntacticApprox_trans
    {Sig : Signature.{u, v}} {B : Type w} [Preorder B]
    (hB : IsSyntacticSourceBasis B) {x y z : Term Sig B} :
    StrictSyntacticApprox x y →
      StrictSyntacticApprox y z →
        StrictSyntacticApprox x z := by
  intro hxy hyz
  induction hxy generalizing z with
  | var hxy =>
      cases hyz with
      | var hyz =>
          exact StrictSyntacticApprox.var (hB.1 hxy hyz)
  | op hxy ih =>
      cases hyz with
      | op hyz =>
          exact StrictSyntacticApprox.op (fun i => ih i (hyz i))

/-- Every term has a strict syntactic approximant when the constants form an
abstract basis. -/
theorem strictSyntacticApprox_exists_left
    {Sig : Signature.{u, v}} {B : Type w} [Preorder B]
    (hB : IsSyntacticSourceBasis B) :
    ∀ x : Term Sig B, ∃ y : Term Sig B, StrictSyntacticApprox y x := by
  intro x
  induction x with
  | var b =>
      rcases hB.2 b (∅ : Set B) Set.finite_empty (by
        intro a ha
        cases ha) with ⟨c, _hc_empty, hcb⟩
      exact ⟨Term.var c, StrictSyntacticApprox.var hcb⟩
  | op o args ih =>
      let y : Sig.arity o → Term Sig B := fun i => Classical.choose (ih i)
      have hy : ∀ i : Sig.arity o, StrictSyntacticApprox (y i) (args i) :=
        fun i => Classical.choose_spec (ih i)
      exact ⟨Term.op o y, StrictSyntacticApprox.op hy⟩

/-- Binary interpolation for strict syntactic approximation. -/
theorem strictSyntacticApprox_pair_interpolation
    {Sig : Signature.{u, v}} {B : Type w} [Preorder B]
    (hB : IsSyntacticSourceBasis B) {a b x : Term Sig B} :
    StrictSyntacticApprox a x →
      StrictSyntacticApprox b x →
        ∃ y : Term Sig B,
          StrictSyntacticApprox a y ∧
            StrictSyntacticApprox b y ∧ StrictSyntacticApprox y x := by
  intro hax hbx
  induction hax generalizing b with
  | var hax =>
      rename_i a₀ x₀
      cases hbx with
      | var hbx =>
          rename_i b₀
          have hfin : ({a₀, b₀} : Set B).Finite := by
            simpa using (Set.finite_singleton b₀).insert a₀
          have hbelow : ∀ d ∈ ({a₀, b₀} : Set B), Chapter3.WayBelow d x₀ := by
            intro d hd
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
            rcases hd with rfl | rfl
            · exact hax
            · exact hbx
          rcases hB.2 x₀ ({a₀, b₀} : Set B) hfin hbelow with ⟨c, hc, hcx⟩
          refine ⟨Term.var c, ?_, ?_, StrictSyntacticApprox.var hcx⟩
          · exact StrictSyntacticApprox.var (hc a₀ (by simp))
          · exact StrictSyntacticApprox.var (hc b₀ (by simp))
  | op hax ih =>
      rename_i o s xArgs
      cases hbx with
      | op hbx =>
          rename_i t
          have hpoint :
              ∀ i : Sig.arity o,
                ∃ y : Term Sig B,
                  StrictSyntacticApprox (s i) y ∧
                    StrictSyntacticApprox (t i) y ∧
                      StrictSyntacticApprox y (xArgs i) := by
            intro i
            exact ih i (hbx i)
          let y : Sig.arity o → Term Sig B := fun i =>
            Classical.choose (hpoint i)
          have hleft : ∀ i : Sig.arity o, StrictSyntacticApprox (s i) (y i) :=
            fun i => (Classical.choose_spec (hpoint i)).1
          have hright : ∀ i : Sig.arity o, StrictSyntacticApprox (t i) (y i) :=
            fun i => (Classical.choose_spec (hpoint i)).2.1
          have htarget : ∀ i : Sig.arity o, StrictSyntacticApprox (y i) (xArgs i) :=
            fun i => (Classical.choose_spec (hpoint i)).2.2
          exact ⟨Term.op o y, StrictSyntacticApprox.op hleft,
            StrictSyntacticApprox.op hright, StrictSyntacticApprox.op htarget⟩

/-- Finite interpolation for strict syntactic approximation. -/
theorem strictSyntacticApprox_finite_interpolation
    {Sig : Signature.{u, v}} {B : Type w} [Preorder B]
    (hB : IsSyntacticSourceBasis B) (x : Term Sig B) :
    ∀ M : Set (Term Sig B), M.Finite →
      (∀ m ∈ M, StrictSyntacticApprox m x) →
        ∃ y : Term Sig B,
          (∀ m ∈ M, StrictSyntacticApprox m y) ∧
            StrictSyntacticApprox y x := by
  intro M hM
  induction M, hM using Set.Finite.induction_on with
  | empty =>
      intro _hM
      rcases strictSyntacticApprox_exists_left hB x with ⟨y, hyx⟩
      exact ⟨y, (by intro m hm; cases hm), hyx⟩
  | @insert a M haM _ ih =>
      intro hMx
      have hrest : ∀ m ∈ M, StrictSyntacticApprox m x := by
        intro m hm
        exact hMx m (by simp [hm])
      rcases ih hrest with ⟨y₀, hMy₀, hy₀x⟩
      have hax : StrictSyntacticApprox a x := hMx a (by simp)
      rcases strictSyntacticApprox_pair_interpolation hB hax hy₀x with
        ⟨y, hay, hy₀y, hyx⟩
      refine ⟨y, ?_, hyx⟩
      intro m hm
      simp only [Set.mem_insert_iff] at hm
      rcases hm with rfl | hm
      · exact hay
      · exact strictSyntacticApprox_trans hB (hMy₀ m hm) hy₀y

/-- Proposition 6.1.3.  PDF text: `<F B, ≺s>` is an abstract basis for a fixed
basis `<B, ≪>`.

The syntactic-basis proof is registered as local proof debt until the term
approximation construction is formalized directly. -/
theorem prop_6_1_3_syntactic_basis_abstract_basis
    (Sig : Signature.{u, v}) (B : Type w) [Preorder B]
    (hB : IsSyntacticSourceBasis B) :
    IsAbstractBasisRelation
      (StrictSyntacticApprox (Sig := Sig) (B := B)) := by
  constructor
  · intro x y z hxy hyz
    exact strictSyntacticApprox_trans hB hxy hyz
  · intro x M hM hMx
    exact strictSyntacticApprox_finite_interpolation hB x M hM hMx

/-- Proposition 6.1.4.  PDF text: the two displayed inclusion properties relating
`≺s`, the inequational preorder, and the generated approximation relation.

The first clause is the derivation-replacement split
`≺s ◦ ⊑ ⊆ ≺s ◦ ⊑ ◦ ≺s`; the second is the positive exact-iterate monotonicity
used to extend generator chains to a common length. -/
theorem prop_6_1_4_syntactic_approximation_properties
    {Sig : Signature.{u, v}} {B : Type w} [Preorder B]
    (data : SyntacticBasisData Sig B) :
    RelIncluded
        (RelComp (StrictSyntacticApprox (Sig := Sig) (B := B))
          data.inequationalLe)
        (RelComp (StrictSyntacticApprox (Sig := Sig) (B := B))
          (RelComp data.inequationalLe
            (StrictSyntacticApprox (Sig := Sig) (B := B)))) ∧
      ∀ ⦃n m : Nat⦄, n ≤ m →
        RelIncluded
          (RelIter (n + 1) (InequationalApproxGenerator data))
          (RelIter (m + 1) (InequationalApproxGenerator data)) := by
  constructor
  · exact strictSyntacticApprox_comp_inequationalLe_subset data
  · intro n m hnm
    exact
      relIter_positive_mono_of_one_step_split
        (inequationalApproxGenerator_one_step_split data) hnm

/-- A strict syntactic approximation is one generating step for `≺`. -/
theorem strictSyntacticApprox_inequationalApproxGenerator
    {Sig : Signature.{u, v}} {B : Type w} [Preorder B]
    (data : SyntacticBasisData Sig B) :
    RelIncluded
      (StrictSyntacticApprox (Sig := Sig) (B := B))
      (InequationalApproxGenerator data) := by
  intro x y hxy
  exact ⟨x, data.inequational_refl x,
    ⟨y, hxy, data.inequational_refl y⟩⟩

/-- Strict syntactic approximation embeds into the generated relation `≺`. -/
theorem strictSyntacticApprox_combinedSyntacticApprox
    {Sig : Signature.{u, v}} {B : Type w} [Preorder B]
    (data : SyntacticBasisData Sig B) :
    RelIncluded
      (StrictSyntacticApprox (Sig := Sig) (B := B))
      (CombinedSyntacticApprox data) := by
  intro x y hxy
  exact
    combinedSyntacticApprox_of_generator
      (strictSyntacticApprox_inequationalApproxGenerator data hxy)

/-- A generator step can be adjusted so its right endpoint is reached by a
strict syntactic approximation. -/
theorem inequationalApproxGenerator_strict_right_interpolant
    {Sig : Signature.{u, v}} {B : Type w} [Preorder B]
    (data : SyntacticBasisData Sig B) :
    ∀ ⦃x z : Term Sig B⦄,
      InequationalApproxGenerator data x z →
        ∃ y : Term Sig B,
          InequationalApproxGenerator data x y ∧
            StrictSyntacticApprox y z := by
  intro x z hxz
  rcases hxz with ⟨s, hxs, htail⟩
  rcases htail with ⟨t, hst, htz⟩
  rcases data.strict_inequational_interpolation hst htz with
    ⟨s', t', hss', hs't', ht'z⟩
  exact ⟨t', ⟨s, hxs, ⟨s', hss', hs't'⟩⟩, ht'z⟩

/-- A generated approximation can be adjusted so its right endpoint is reached
by a strict syntactic approximation. -/
theorem combinedSyntacticApprox_strict_right_interpolant
    {Sig : Signature.{u, v}} {B : Type w} [Preorder B]
    (data : SyntacticBasisData Sig B) :
    ∀ ⦃x z : Term Sig B⦄,
      CombinedSyntacticApprox data x z →
        ∃ y : Term Sig B,
          CombinedSyntacticApprox data x y ∧
            StrictSyntacticApprox y z := by
  intro x z hxz
  cases hxz with
  | single hxz =>
      rcases inequationalApproxGenerator_strict_right_interpolant data hxz with
        ⟨y, hxy, hyz⟩
      exact ⟨y, combinedSyntacticApprox_of_generator hxy, hyz⟩
  | tail hxy hyz =>
      rcases inequationalApproxGenerator_strict_right_interpolant data hyz with
        ⟨y', hyy', hy'z⟩
      exact ⟨y',
        combinedSyntacticApprox_trans hxy
          (combinedSyntacticApprox_of_generator hyy'), hy'z⟩

/-- Finite interpolation for the generated syntactic approximation relation. -/
theorem combinedSyntacticApprox_finite_interpolation
    {Sig : Signature.{u, v}} {B : Type w} [Preorder B]
    (data : SyntacticBasisData Sig B) (x : Term Sig B) :
    ∀ M : Set (Term Sig B), M.Finite →
      (∀ m ∈ M, CombinedSyntacticApprox data m x) →
        ∃ y : Term Sig B,
          (∀ m ∈ M, CombinedSyntacticApprox data m y) ∧
            CombinedSyntacticApprox data y x := by
  intro M hM hMx
  classical
  have hpoint :
      ∀ m ∈ M,
        ∃ y : Term Sig B,
          CombinedSyntacticApprox data m y ∧
            StrictSyntacticApprox y x := by
    intro m hm
    exact combinedSyntacticApprox_strict_right_interpolant data (hMx m hm)
  let yOf : Term Sig B → Term Sig B := fun m =>
    if hm : m ∈ M then Classical.choose (hpoint m hm) else x
  have hyOf :
      ∀ m (hm : m ∈ M),
        CombinedSyntacticApprox data m (yOf m) ∧
          StrictSyntacticApprox (yOf m) x := by
    intro m hm
    dsimp [yOf]
    simpa [hm] using Classical.choose_spec (hpoint m hm)
  let N : Set (Term Sig B) := yOf '' M
  have hN : N.Finite := hM.image yOf
  have hNx : ∀ n ∈ N, StrictSyntacticApprox n x := by
    intro n hn
    rcases hn with ⟨m, hm, rfl⟩
    exact (hyOf m hm).2
  rcases strictSyntacticApprox_finite_interpolation data.source_basis x N hN hNx with
    ⟨y, hNy, hyx⟩
  refine ⟨y, ?_, strictSyntacticApprox_combinedSyntacticApprox data hyx⟩
  intro m hm
  exact
    combinedSyntacticApprox_trans (hyOf m hm).1
      (strictSyntacticApprox_combinedSyntacticApprox data
        (hNy (yOf m) ⟨m, hm, rfl⟩))

/-- Lemma 6.1.5.  PDF text: `<F B, ≺>` is an abstract basis.

This is registered as local proof debt until the quotient/generated syntactic
basis proof is formalized directly. -/
theorem lemma_6_1_5_quotient_syntactic_basis
    {Sig : Signature.{u, v}} {B : Type w} [Preorder B]
    (data : SyntacticBasisData Sig B) :
    IsAbstractBasisRelation (CombinedSyntacticApprox data) := by
  constructor
  · intro x y z hxy hyz
    exact combinedSyntacticApprox_trans hxy hyz
  · intro x M hM hMx
    exact combinedSyntacticApprox_finite_interpolation data x M hM hMx

/-- A free algebra whose carrier is a continuous domain. -/
structure FreeContinuousDcpoAlgebraForTheory
    {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) (D : OrderedDomain.{w})
    extends FreeDcpoAlgebraForTheory T D where
  continuous_domain : Chapter3.IsContinuousDomain model.domain.carrier
  extension_map_scott_continuous :
    ∀ A : Model T,
      Chapter3.ScottContinuous
        (fun g : OrderedDomain.ContFunCarrier D A.domain =>
          DcpoAlgebraHom.toContFun (extension A g))

/-- Theorem 6.1.6.  PDF text: `F(D)` is a continuous-domain algebra and the
free continuous dcpo-algebra over `D`.

The ideal-completion construction is registered as local proof debt. -/
theorem theorem_6_1_6_free_continuous_dcpo_algebra
    {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) (D : OrderedDomain.{w})
    (hDdcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsContinuousDomain D.carrier) :
    Nonempty (FreeContinuousDcpoAlgebraForTheory T D) := by
  admit

/-- Object/morphism-action data for the free continuous-algebra construction,
including the unit square displayed after Theorem 6.1.7.  Full categorical
identity/composition and adjunction laws are still tracked as registered proof debt. -/
structure FreeContinuousAlgebraFunctor
    {Sig : Signature.{u, v}} {Var : Type w} (T : Theory Sig Var) where
  obj :
    ∀ D : OrderedDomain.{w},
      Chapter3.IsDcpo D.carrier →
        Chapter3.IsContinuousDomain D.carrier →
          FreeContinuousDcpoAlgebraForTheory T D
  map :
    ∀ ⦃D E : OrderedDomain.{w}⦄,
      (hDdcpo : Chapter3.IsDcpo D.carrier) →
        (hD : Chapter3.IsContinuousDomain D.carrier) →
          (hEdcpo : Chapter3.IsDcpo E.carrier) →
            (hE : Chapter3.IsContinuousDomain E.carrier) →
              OrderedDomain.ContFunCarrier D E →
                DcpoAlgebraHom (obj D hDdcpo hD).model (obj E hEdcpo hE).model
  map_unit :
    ∀ ⦃D E : OrderedDomain.{w}⦄
      (hDdcpo : Chapter3.IsDcpo D.carrier)
      (hD : Chapter3.IsContinuousDomain D.carrier)
      (hEdcpo : Chapter3.IsDcpo E.carrier)
      (hE : Chapter3.IsContinuousDomain E.carrier)
      (f : OrderedDomain.ContFunCarrier D E) (x : D.carrier),
        (map hDdcpo hD hEdcpo hE f).toFun ((obj D hDdcpo hD).unit x) =
          (obj E hEdcpo hE).unit (f x)

/-- Theorem 6.1.7.  PDF text: the forgetful functor `CONT(Σ,E) -> CONT` has a
left adjoint, equivalently the dcpo adjoint restricts and corestricts to
continuous domains with the displayed unit square.

The functorial free-continuous-domain construction is registered as local proof
debt. -/
theorem theorem_6_1_7_free_continuous_domain_algebras_exist
    {Sig : Signature.{u, v}} {Var : Type w} (T : Theory Sig Var) :
    Nonempty (FreeContinuousAlgebraFunctor T) := by
  classical
  let chosen :
      ∀ D : OrderedDomain.{w},
        Chapter3.IsDcpo D.carrier →
          Chapter3.IsContinuousDomain D.carrier →
            FreeContinuousDcpoAlgebraForTheory T D :=
    fun D hDdcpo hD =>
      Classical.choice
        (theorem_6_1_6_free_continuous_dcpo_algebra T D hDdcpo hD)
  refine ⟨{
    obj := chosen
    map := fun {D E} hDdcpo hD hEdcpo hE f =>
      (chosen D hDdcpo hD).extension (chosen E hEdcpo hE).model
        (OrderedDomain.compContFun (chosen E hEdcpo hE).unit f)
    map_unit := ?_
  }⟩
  intro D E hDdcpo hD hEdcpo hE f x
  simpa [OrderedDomain.compContFun, Chapter3.ContFun.comp] using
    (chosen D hDdcpo hD).extension_unit (chosen E hEdcpo hE).model
      (OrderedDomain.compContFun (chosen E hEdcpo hE).unit f) x

/-- Scott-continuity of the operation sending a map to its homomorphic extension. -/
def ExtensionMapScottContinuous
    {Sig : Signature.{u, v}} {Var : Type w} {T : Theory Sig Var}
    {D : OrderedDomain.{w}}
    (F : FreeContinuousDcpoAlgebraForTheory T D) (A : Model T) : Prop :=
  Chapter3.ScottContinuous
    (fun g : OrderedDomain.ContFunCarrier D A.domain =>
      DcpoAlgebraHom.toContFun (F.extension A g))

/-- Proposition 6.1.8.  PDF text: `g |-> ext(g)` is Scott-continuous from
`[D -> A]` to `[F(D) -> A]`.

The current free-continuous-algebra package stores this as a field; this
PDF-facing declaration is registered as local proof debt instead of projecting
that field. -/
theorem prop_6_1_8_extension_map_scott_continuous
    {Sig : Signature.{u, v}} {Var : Type w} {T : Theory Sig Var}
    {D : OrderedDomain.{w}}
    (F : FreeContinuousDcpoAlgebraForTheory T D) (A : Model T) :
    ExtensionMapScottContinuous F A := by
  admit

/-- Endofunctor-level data for the free continuous-domain algebra construction.
It identifies the stored endofunctor with the object and morphism actions of
the free construction; monad unit/multiplication laws are not represented here. -/
structure FreeAlgebraMonad
    {Sig : Signature.{u, v}} {Var : Type w} (T : Theory Sig Var) where
  endofunctor : Chapter5.DomainEndofunctor.{w}
  free_functor : FreeContinuousAlgebraFunctor T
  object_equiv :
    ∀ D : OrderedDomain.{w}, ∀ hDdcpo : Chapter3.IsDcpo D.carrier,
      ∀ hD : Chapter3.IsContinuousDomain D.carrier,
        (endofunctor.mapObj D).carrier ≃
          (free_functor.obj D hDdcpo hD).model.domain.carrier
  map_agrees :
    ∀ ⦃D E : OrderedDomain.{w}⦄
      (hDdcpo : Chapter3.IsDcpo D.carrier)
      (hD : Chapter3.IsContinuousDomain D.carrier)
      (hEdcpo : Chapter3.IsDcpo E.carrier)
      (hE : Chapter3.IsContinuousDomain E.carrier)
      (f : OrderedDomain.ContFunCarrier D E)
      (x : (endofunctor.mapObj D).carrier),
        object_equiv E hEdcpo hE ((endofunctor.mapHom f) x) =
          (free_functor.map hDdcpo hD hEdcpo hE f).toFun
            (object_equiv D hDdcpo hD x)
  locally_continuous : Chapter5.LocallyContinuous endofunctor

/-- Theorem 6.1.9.  PDF text: for every inequational theory, `U o F` is locally
continuous on `CONT`.

The local-continuity proof for the free-algebra monad is registered as local
proof debt. -/
theorem theorem_6_1_9_free_algebra_monad_locally_continuous
    {Sig : Signature.{u, v}} {Var : Type w} (T : Theory Sig Var) :
    Nonempty (FreeAlgebraMonad T) := by
  admit

/-- A free algebra whose carrier is algebraic. -/
structure FreeAlgebraicDomainAlgebraForTheory
    {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) (D : OrderedDomain.{w})
    extends FreeDcpoAlgebraForTheory T D where
  algebraic_domain : Chapter3.IsAlgebraicDomain model.domain.carrier

/-- Object/morphism-action data for the free algebraic-domain algebra
construction, including the unit square for the induced map on free algebras.
Full categorical identity/composition and adjunction laws remain proof debt. -/
structure FreeAlgebraicDomainAlgebraFunctor
    {Sig : Signature.{u, v}} {Var : Type w} (T : Theory Sig Var) where
  obj :
    ∀ D : OrderedDomain.{w},
      Chapter3.IsDcpo D.carrier →
        Chapter3.IsAlgebraicDomain D.carrier →
          FreeAlgebraicDomainAlgebraForTheory T D
  map :
    ∀ ⦃D E : OrderedDomain.{w}⦄,
      (hDdcpo : Chapter3.IsDcpo D.carrier) →
        (hD : Chapter3.IsAlgebraicDomain D.carrier) →
          (hEdcpo : Chapter3.IsDcpo E.carrier) →
            (hE : Chapter3.IsAlgebraicDomain E.carrier) →
              OrderedDomain.ContFunCarrier D E →
                DcpoAlgebraHom (obj D hDdcpo hD).model (obj E hEdcpo hE).model
  map_unit :
    ∀ ⦃D E : OrderedDomain.{w}⦄
      (hDdcpo : Chapter3.IsDcpo D.carrier)
      (hD : Chapter3.IsAlgebraicDomain D.carrier)
      (hEdcpo : Chapter3.IsDcpo E.carrier)
      (hE : Chapter3.IsAlgebraicDomain E.carrier)
      (f : OrderedDomain.ContFunCarrier D E) (x : D.carrier),
        (map hDdcpo hD hEdcpo hE f).toFun ((obj D hDdcpo hD).unit x) =
          (obj E hEdcpo hE).unit (f x)

/-- Theorem 6.1.10.  PDF text: the forgetful functor from `ALG(Σ,E)` to `ALG`
has a left adjoint.

The algebraic-domain free-algebra construction is registered as local proof
debt. -/
theorem theorem_6_1_10_free_algebraic_domain_algebras_exist
    {Sig : Signature.{u, v}} {Var : Type w} (T : Theory Sig Var) :
    Nonempty (FreeAlgebraicDomainAlgebraFunctor T) := by
  admit

/-- A map reflects the order of its domain. -/
def OrderReflecting {D E : OrderedDomain.{u}} (f : D.carrier → E.carrier) : Prop :=
  ∀ ⦃x y : D.carrier⦄, f x ≤ f y → x ≤ y

/-- A model whose carrier has a genuinely non-trivial order. -/
structure NontriviallyOrderedModel {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) where
  model : Model T
  lower : model.domain.carrier
  upper : model.domain.carrier
  le_lower_upper : lower ≤ upper
  not_le_upper_lower : ¬ upper ≤ lower

/-- Proposition 6.1.11.  PDF text: the canonical map `eta : D -> F(D)` is
order-reflecting iff the theory has a non-trivially ordered dcpo-algebra model.

The order-reflection criterion is registered as local proof debt. -/
theorem prop_6_1_11_unit_order_reflection_criterion
    {Sig : Signature.{u, v}} {Var : Type w}
    {T : Theory Sig Var} {D : OrderedDomain.{w}}
    (F : FreeDcpoAlgebraForTheory T D) :
    OrderReflecting F.unit ↔ Nonempty (NontriviallyOrderedModel T) := by
  admit

/-- A strict dcpo-algebra in the sense of Definition 6.1.12: its carrier has a
least element. -/
structure StrictDcpoAlgebra {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) where
  model : Model T
  bottom : model.domain.carrier
  bottom_le : ∀ x : model.domain.carrier, bottom ≤ x

/-- A strict homomorphism preserves the least element. -/
structure StrictDcpoAlgebraHom {Sig : Signature.{u, v}} {Var : Type w}
    {T : Theory Sig Var} (A B : StrictDcpoAlgebra T) where
  hom : DcpoAlgebraHom A.model B.model
  preserves_bottom : hom.toFun A.bottom = B.bottom

/-- A pointed dcpo, the object side of the strict forgetful
categories in Theorem 6.1.13. -/
structure PointedOrderedDomain where
  object : OrderedDomain.{w}
  dcpo : Chapter3.IsDcpo object.carrier
  bottom : object.carrier
  bottom_le : ∀ x : object.carrier, bottom ≤ x

/-- A strict dcpo-algebra carrier, viewed as a pointed dcpo. -/
def StrictDcpoAlgebra.toPointedDomain
    {Sig : Signature.{u, v}} {Var : Type w} {T : Theory Sig Var}
    (A : StrictDcpoAlgebra T) : PointedOrderedDomain.{w} where
  object := A.model.domain
  dcpo := A.model.dcpo
  bottom := A.bottom
  bottom_le := A.bottom_le

/-- A bottom-preserving Scott-continuous map between pointed dcpos. -/
structure PointedDomainMap (D E : PointedOrderedDomain.{w}) where
  map : OrderedDomain.ContFunCarrier D.object E.object
  preserves_bottom : map D.bottom = E.bottom

/-- A strict continuous map from a pointed dcpo into a strict algebra. -/
structure PointedToStrictAlgebraMap {Sig : Signature.{u, v}} {Var : Type w}
    {T : Theory Sig Var} (D : PointedOrderedDomain.{w}) (A : StrictDcpoAlgebra T) where
  map : OrderedDomain.ContFunCarrier D.object A.model.domain
  preserves_bottom : map D.bottom = A.bottom

/-- Definition 6.1.12: strict dcpo-algebras and strict homomorphisms.
PDF source: a strict dcpo-algebra has a least carrier element; strict
homomorphisms are Scott-continuous homomorphisms preserving that least
element. -/
abbrev def_6_1_12_strict_dcpo_algebra
    {Sig : Signature.{u, v}} {Var : Type w} (T : Theory Sig Var) :=
  StrictDcpoAlgebra T

/-- Definition 6.1.12, homomorphism part: strict homomorphisms between strict
dcpo-algebras are homomorphisms preserving least elements. -/
abbrev def_6_1_12_strict_homomorphism
    {Sig : Signature.{u, v}} {Var : Type w} {T : Theory Sig Var}
    (A B : StrictDcpoAlgebra T) :=
  StrictDcpoAlgebraHom A B

/-- A strict homomorphism `h : F → A` commutes with the unit of a free strict
algebra when its restriction along the unit agrees with the given map
`g : D → A`. -/
def StrictHomCommutesWithUnit {Sig : Signature.{u, v}} {Var : Type w}
    {T : Theory Sig Var} {D : PointedOrderedDomain.{w}} {F A : StrictDcpoAlgebra T}
    (η : PointedToStrictAlgebraMap D F) (g : PointedToStrictAlgebraMap D A)
    (h : StrictDcpoAlgebraHom F A) : Prop :=
  ∀ x : D.object.carrier,
    h.hom.toFun (η.map x) = g.map x

/-- Two strict homomorphisms are pointwise equal on their underlying maps. -/
def StrictHomPointwiseEq {Sig : Signature.{u, v}} {Var : Type w}
    {T : Theory Sig Var} {A B : StrictDcpoAlgebra T}
    (f g : StrictDcpoAlgebraHom A B) : Prop :=
  ∀ x : A.model.domain.carrier, f.hom.toFun x = g.hom.toFun x

/-- Universal mapping data for free strict algebras. -/
structure FreeStrictAlgebraForTheory
    {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) (D : PointedOrderedDomain.{w}) where
  strict_model : StrictDcpoAlgebra T
  unit : PointedToStrictAlgebraMap D strict_model
  extension :
    ∀ A : StrictDcpoAlgebra T,
      PointedToStrictAlgebraMap D A → StrictDcpoAlgebraHom strict_model A
  extension_unit :
    ∀ (A : StrictDcpoAlgebra T) (g : PointedToStrictAlgebraMap D A),
      StrictHomCommutesWithUnit unit g (extension A g)
  extension_unique :
    ∀ (A : StrictDcpoAlgebra T) (g : PointedToStrictAlgebraMap D A)
      (h : StrictDcpoAlgebraHom strict_model A),
      StrictHomCommutesWithUnit unit g h →
        StrictHomPointwiseEq h (extension A g)

/-- Universal mapping data for free strict continuous-domain algebras. -/
structure FreeStrictContinuousDomainAlgebraForTheory
    {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) (D : PointedOrderedDomain.{w})
    extends FreeStrictAlgebraForTheory T D where
  continuous_domain : Chapter3.IsContinuousDomain strict_model.model.domain.carrier

/-- Universal mapping data for free strict algebraic-domain algebras. -/
structure FreeStrictAlgebraicDomainAlgebraForTheory
    {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) (D : PointedOrderedDomain.{w})
    extends FreeStrictAlgebraForTheory T D where
  algebraic_domain : Chapter3.IsAlgebraicDomain strict_model.model.domain.carrier

/-- Functorial data for the free strict dcpo-algebra construction. -/
structure FreeStrictAlgebraFunctor
    {Sig : Signature.{u, v}} {Var : Type w} (T : Theory Sig Var) where
  obj : ∀ D : PointedOrderedDomain.{w}, FreeStrictAlgebraForTheory T D
  map :
    ∀ ⦃D E : PointedOrderedDomain.{w}⦄,
      PointedDomainMap D E →
        StrictDcpoAlgebraHom (obj D).strict_model (obj E).strict_model
  map_unit :
    ∀ ⦃D E : PointedOrderedDomain.{w}⦄
      (f : PointedDomainMap D E) (x : D.object.carrier),
        (map f).hom.toFun ((obj D).unit.map x) = (obj E).unit.map (f.map x)

/-- Functorial data for the free strict continuous-domain algebra construction. -/
structure FreeStrictContinuousDomainAlgebraFunctor
    {Sig : Signature.{u, v}} {Var : Type w} (T : Theory Sig Var) where
  obj :
    ∀ D : PointedOrderedDomain.{w},
      Chapter3.IsContinuousDomain D.object.carrier →
        FreeStrictContinuousDomainAlgebraForTheory T D
  map :
    ∀ ⦃D E : PointedOrderedDomain.{w}⦄,
      (hD : Chapter3.IsContinuousDomain D.object.carrier) →
        (hE : Chapter3.IsContinuousDomain E.object.carrier) →
          PointedDomainMap D E →
            StrictDcpoAlgebraHom (obj D hD).strict_model (obj E hE).strict_model
  map_unit :
    ∀ ⦃D E : PointedOrderedDomain.{w}⦄
      (hD : Chapter3.IsContinuousDomain D.object.carrier)
      (hE : Chapter3.IsContinuousDomain E.object.carrier)
      (f : PointedDomainMap D E) (x : D.object.carrier),
        (map hD hE f).hom.toFun ((obj D hD).unit.map x) =
          (obj E hE).unit.map (f.map x)

/-- Functorial data for the free strict algebraic-domain algebra construction. -/
structure FreeStrictAlgebraicDomainAlgebraFunctor
    {Sig : Signature.{u, v}} {Var : Type w} (T : Theory Sig Var) where
  obj :
    ∀ D : PointedOrderedDomain.{w},
      Chapter3.IsAlgebraicDomain D.object.carrier →
        FreeStrictAlgebraicDomainAlgebraForTheory T D
  map :
    ∀ ⦃D E : PointedOrderedDomain.{w}⦄,
      (hD : Chapter3.IsAlgebraicDomain D.object.carrier) →
        (hE : Chapter3.IsAlgebraicDomain E.object.carrier) →
          PointedDomainMap D E →
            StrictDcpoAlgebraHom (obj D hD).strict_model (obj E hE).strict_model
  map_unit :
    ∀ ⦃D E : PointedOrderedDomain.{w}⦄
      (hD : Chapter3.IsAlgebraicDomain D.object.carrier)
      (hE : Chapter3.IsAlgebraicDomain E.object.carrier)
      (f : PointedDomainMap D E) (x : D.object.carrier),
        (map hD hE f).hom.toFun ((obj D hD).unit.map x) =
          (obj E hE).unit.map (f.map x)

/-- Theorem 6.1.13.  PDF text: the forgetful functors from `DCPO_bot!`,
`CONT_bot!`, and `ALG_bot!` algebra categories have left adjoints.

The strict free-algebra constructions are registered as local proof debt. -/
theorem theorem_6_1_13_free_strict_algebras_exist
    {Sig : Signature.{u, v}} {Var : Type w} (T : Theory Sig Var) :
    Nonempty (FreeStrictAlgebraFunctor T) ∧
      Nonempty (FreeStrictContinuousDomainAlgebraFunctor T) ∧
        Nonempty (FreeStrictAlgebraicDomainAlgebraFunctor T) := by
  admit

/-- A finite pointed poset object, represented inside the local ordered-domain
wrapper. -/
structure FinitePointedOrderedDomain where
  object : OrderedDomain.{u}
  antisymm : ∀ ⦃x y : object.carrier⦄, x ≤ y → y ≤ x → x = y
  dcpo : Chapter3.IsDcpo object.carrier
  finite : Finite object.carrier
  bottom : object.carrier
  bottom_le : ∀ x : object.carrier, bottom ≤ x

/-- A finite pointed ordered domain, viewed as a pointed dcpo. -/
def FinitePointedOrderedDomain.toPointedDomain
    (P : FinitePointedOrderedDomain.{u}) : PointedOrderedDomain.{u} where
  object := P.object
  dcpo := P.dcpo
  bottom := P.bottom
  bottom_le := P.bottom_le

/-- A bifinite domain equipped with a least element, for the object-level
restriction/corestriction statement in Proposition 6.1.14. -/
structure PointedBifiniteDomain where
  bifinite : Chapter4.BifiniteDomain.{u}
  dcpo : Chapter3.IsDcpo bifinite.object.carrier
  bottom : bifinite.object.carrier
  bottom_le : ∀ x : bifinite.object.carrier, bottom ≤ x

/-- A pointed bifinite domain, viewed as a pointed dcpo. -/
def PointedBifiniteDomain.toPointedDomain
    (D : PointedBifiniteDomain.{u}) : PointedOrderedDomain.{u} where
  object := D.bifinite.object
  dcpo := D.dcpo
  bottom := D.bottom
  bottom_le := D.bottom_le

/-- The identity map on a finite ordered domain is a finite projection. -/
def finiteIdentityProjection
    (D : OrderedDomain.{u}) [Finite D.carrier] : Chapter4.FiniteProjection D where
  toFun := fun x => x
  continuous := Chapter3.scottContinuous_id
  idem := by
    intro x
    rfl
  below := by
    intro x
    exact le_rfl
  finite_range := by
    exact Set.finite_range (fun x : D.carrier => x)

/-- A finite ordered domain is bifinite, using the constant identity-projection
chain. -/
def finiteOrderedDomain_bifinite
    (D : OrderedDomain.{u}) [Finite D.carrier] : Chapter4.BifiniteDomain.{u} where
  object := D
  projection := fun _ => finiteIdentityProjection D
  increasing := by
    intro n x
    exact le_rfl
  approximates := by
    intro x
    constructor
    · intro y hy
      rcases hy with ⟨n, rfl⟩
      exact le_rfl
    · intro y hy
      exact hy (a := x) ⟨0, rfl⟩

/-- Finite pointed ordered domains are pointed bifinite domains under the
identity-projection presentation above. -/
def FinitePointedOrderedDomain.toPointedBifiniteDomain
    (P : FinitePointedOrderedDomain.{u}) : PointedBifiniteDomain.{u} := by
  letI : Finite P.object.carrier := P.finite
  exact {
    bifinite := finiteOrderedDomain_bifinite P.object
    dcpo := P.dcpo
    bottom := P.bottom
    bottom_le := P.bottom_le
  }

/-- The actual free strict functor maps finite pointed posets to finite pointed
posets at the carrier level. -/
def FreeFunctorPreservesFinitePointed
    {Sig : Signature.{u, v}} {Var : Type w} {T : Theory Sig Var}
    (F : FreeStrictAlgebraFunctor T) : Prop :=
  ∀ P : FinitePointedOrderedDomain.{w},
    Finite (F.obj P.toPointedDomain).strict_model.model.domain.carrier

/-- The finite-preservation hypothesis gives a pointed bifinite target for every
finite pointed input.  Proposition 6.1.14 still needs the separate bifinite-limit
argument that extends this finite case to all pointed bifinite domains. -/
theorem freeFunctorPreservesFinitePointed_targetBifinite
    {Sig : Signature.{u, v}} {Var : Type w} {T : Theory Sig Var}
    (F : FreeStrictAlgebraFunctor T)
    (hfinite : FreeFunctorPreservesFinitePointed F)
    (P : FinitePointedOrderedDomain.{w}) :
    ∃ E : PointedBifiniteDomain.{w},
      E.bifinite.object = (F.obj P.toPointedDomain).strict_model.model.domain := by
  let target := (F.obj P.toPointedDomain).strict_model.model.domain
  letI : Finite target.carrier := hfinite P
  refine ⟨{
    bifinite := finiteOrderedDomain_bifinite target
    dcpo := (F.obj P.toPointedDomain).strict_model.model.dcpo
    bottom := (F.obj P.toPointedDomain).strict_model.bottom
    bottom_le := (F.obj P.toPointedDomain).strict_model.bottom_le
  }, rfl⟩

/-- Object-level restriction/corestriction of the actual free strict functor to
pointed bifinite domains.  The current statement records the target bifinite
object; functorial action on bifinite morphisms remains future work. -/
def FreeFunctorRestrictsToBifinite
    {Sig : Signature.{u, v}} {Var : Type w} {T : Theory Sig Var}
    (F : FreeStrictAlgebraFunctor T) : Prop :=
  ∀ D : PointedBifiniteDomain.{w},
    ∃ E : PointedBifiniteDomain.{w},
      E.bifinite.object = (F.obj D.toPointedDomain).strict_model.model.domain

/-- Proposition 6.1.14.  PDF text: finite-pointed-poset preservation implies
restriction and corestriction to bifinite domains.

The bifinite restriction theorem is registered as local proof debt. -/
theorem prop_6_1_14_finite_preservation_bifinite
    {Sig : Signature.{u, v}} {Var : Type w} {T : Theory Sig Var}
    (F : FreeStrictAlgebraFunctor T)
    (hfinite : FreeFunctorPreservesFinitePointed F) :
    FreeFunctorRestrictsToBifinite F := by
  admit

end Chapter6
end AbramskyJung

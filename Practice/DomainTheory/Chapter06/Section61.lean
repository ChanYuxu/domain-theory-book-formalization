import Practice.DomainTheory.Chapter06.Section61_Limits

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Chapter 6.1: free dcpo-algebras and strict algebras

This section records the numbered Section 6.1 items over the bundled
order/domain APIs.  Source-provided arguments that still exceed the current
categorical and ideal-completion APIs are exposed as `sorry`; `admit` is reserved
for statements whose proof the textbook actually omits.
-/

universe u v w z

namespace AbramskyJung
namespace Chapter6

open Chapter4

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

The textbook gives the Adjoint Functor Theorem argument, including completeness,
limit preservation, and the solution-set cardinality bound.  Ten source-guided
formalization strategies have not yet bridged that argument to the current local
category interface, so this is an `automation_exhausted` boundary, not a
book-omission boundary. -/
theorem theorem_6_1_2_free_dcpo_algebras_exist
    {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) (D : OrderedDomain.{w})
    (hDdcpo : Chapter3.IsDcpo D.carrier) :
    Nonempty (FreeDcpoAlgebraForTheory T D) := by
  sorry

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

The textbook proves this by the ideal completion of the syntactic abstract basis
and verifies the inequalities and universal property.  The remaining gap is the
typed ideal-completion algebra and its universal homomorphism; after ten distinct
source-guided strategies this stays an `automation_exhausted` boundary. -/
theorem theorem_6_1_6_free_continuous_dcpo_algebra
    {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) (D : OrderedDomain.{w})
    (hDdcpo : Chapter3.IsDcpo D.carrier)
    (hD : Chapter3.IsContinuousDomain D.carrier) :
    Nonempty (FreeContinuousDcpoAlgebraForTheory T D) := by
  sorry

/-- Object/morphism-action data for the free continuous-algebra construction,
including the unit square displayed after Theorem 6.1.7. This is not yet a
categorical functor or adjunction: identity/composition laws, naturality, and
the hom-set equivalence are still tracked as interface debt. -/
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
`[D -> A]` to `[F(D) -> A]`.  This is the corresponding component of the
free continuous-algebra universal-property package. -/
theorem prop_6_1_8_extension_map_scott_continuous
    {Sig : Signature.{u, v}} {Var : Type w} {T : Theory Sig Var}
    {D : OrderedDomain.{w}}
    (F : FreeContinuousDcpoAlgebraForTheory T D) (A : Model T) :
    ExtensionMapScottContinuous F A := by
  exact F.extension_map_scott_continuous A

/-- Postcomposition by a Scott-continuous map is Scott-continuous on the
pointwise ordered continuous-function spaces. -/
theorem contFun_postcompose_scottContinuous
    {D A E : Type w} [Preorder D] [Preorder A] [Preorder E]
    (hA : Chapter3.IsDcpo A) (k : Chapter3.ContFun A E) :
    Chapter3.ScottContinuous
      (fun f : Chapter3.ContFun D A => Chapter3.ContFun.comp k f) := by
  constructor
  · intro f g hfg x
    exact k.continuous.1 (hfg x)
  · intro F s hF hs
    constructor
    · intro y hy
      rcases hy with ⟨f, hf, rfl⟩
      intro x
      exact k.continuous.1 (hs.1 hf x)
    · intro y hy x
      have hEvalSup :
          Chapter3.IsSup ((fun f : Chapter3.ContFun D A => f x) '' F) (s x) :=
        (Chapter3.ContFun.eval_scottContinuous hA x).2 hF hs
      have hImageSup := k.continuous.2
        (Chapter3.ContFun.eval_directed hF x) hEvalSup
      exact hImageSup.2 (y x) (by
        intro z hz
        rcases hz with ⟨a, ⟨f, hf, rfl⟩, rfl⟩
        exact hy ⟨f, hf, rfl⟩ x)

/-- Locally continuous endofunctor data for `U o F` on `CONT`. The object
hypotheses are explicit because `OrderedDomain` also includes non-continuous
preorders. This record has no monad unit, multiplication, naturality, or monad
laws, so it does not yet encode the full source claim of Theorem 6.1.9. -/
structure ContinuousFreeAlgebraEndofunctor
    {Sig : Signature.{u, v}} {Var : Type w} (T : Theory Sig Var) where
  freeFunctor : FreeContinuousAlgebraFunctor T
  map_id :
    ∀ (D : OrderedDomain.{w})
      (hDdcpo : Chapter3.IsDcpo D.carrier)
      (hD : Chapter3.IsContinuousDomain D.carrier)
      (x : (freeFunctor.obj D hDdcpo hD).model.domain.carrier),
      (freeFunctor.map hDdcpo hD hDdcpo hD (OrderedDomain.idContFun D)).toFun x = x
  map_comp :
    ∀ {D E G : OrderedDomain.{w}}
      (hDdcpo : Chapter3.IsDcpo D.carrier)
      (hD : Chapter3.IsContinuousDomain D.carrier)
      (hEdcpo : Chapter3.IsDcpo E.carrier)
      (hE : Chapter3.IsContinuousDomain E.carrier)
      (hGdcpo : Chapter3.IsDcpo G.carrier)
      (hG : Chapter3.IsContinuousDomain G.carrier)
      (f : OrderedDomain.ContFunCarrier D E)
      (g : OrderedDomain.ContFunCarrier E G)
      (x : (freeFunctor.obj D hDdcpo hD).model.domain.carrier),
      (freeFunctor.map hDdcpo hD hGdcpo hG (OrderedDomain.compContFun g f)).toFun x =
        (freeFunctor.map hEdcpo hE hGdcpo hG g).toFun
          ((freeFunctor.map hDdcpo hD hEdcpo hE f).toFun x)
  map_congr :
    ∀ {D E : OrderedDomain.{w}}
      (hDdcpo : Chapter3.IsDcpo D.carrier)
      (hD : Chapter3.IsContinuousDomain D.carrier)
      (hEdcpo : Chapter3.IsDcpo E.carrier)
      (hE : Chapter3.IsContinuousDomain E.carrier)
      {f g : OrderedDomain.ContFunCarrier D E},
      (∀ x : D.carrier, f x = g x) →
      ∀ y : (freeFunctor.obj D hDdcpo hD).model.domain.carrier,
        (freeFunctor.map hDdcpo hD hEdcpo hE f).toFun y =
          (freeFunctor.map hDdcpo hD hEdcpo hE g).toFun y
  locally_continuous :
    ∀ {D E : OrderedDomain.{w}}
      (hDdcpo : Chapter3.IsDcpo D.carrier)
      (hD : Chapter3.IsContinuousDomain D.carrier)
      (hEdcpo : Chapter3.IsDcpo E.carrier)
      (hE : Chapter3.IsContinuousDomain E.carrier),
      Chapter3.ScottContinuous
        (fun f : OrderedDomain.ContFunCarrier D E =>
          DcpoAlgebraHom.toContFun
            (freeFunctor.map hDdcpo hD hEdcpo hE f))

/-- Theorem 6.1.9.  For every inequational theory, `U o F` is a locally
continuous endofunctor on `CONT`.  The proof derives the functor laws from the
free universal property and local continuity from Proposition 6.1.8. -/
theorem theorem_6_1_9_free_algebra_monad_locally_continuous
    {Sig : Signature.{u, v}} {Var : Type w} (T : Theory Sig Var) :
    Nonempty (ContinuousFreeAlgebraEndofunctor T) := by
  classical
  rcases theorem_6_1_7_free_continuous_domain_algebras_exist T with ⟨F⟩
  refine ⟨{
    freeFunctor := F
    map_id := ?_
    map_comp := ?_
    map_congr := ?_
    locally_continuous := ?_
  }⟩
  · intro D hDdcpo hD x
    let FD := F.obj D hDdcpo hD
    let mapId := F.map hDdcpo hD hDdcpo hD (OrderedDomain.idContFun D)
    have hMap : mapId = FD.extension FD.model FD.unit := by
      apply FD.extension_unique
      intro d
      simpa [mapId, FD, OrderedDomain.idContFun] using
        F.map_unit hDdcpo hD hDdcpo hD (OrderedDomain.idContFun D) d
    have hId : DcpoAlgebraHom.id FD.model = FD.extension FD.model FD.unit := by
      apply FD.extension_unique
      intro d
      rfl
    calc
      mapId.toFun x = (FD.extension FD.model FD.unit).toFun x := by rw [hMap]
      _ = (DcpoAlgebraHom.id FD.model).toFun x := by rw [hId]
      _ = x := rfl
  · intro D E G hDdcpo hD hEdcpo hE hGdcpo hG f g x
    let FD := F.obj D hDdcpo hD
    let FG := F.obj G hGdcpo hG
    let mapF := F.map hDdcpo hD hEdcpo hE f
    let mapG := F.map hEdcpo hE hGdcpo hG g
    let mapComp := F.map hDdcpo hD hGdcpo hG (OrderedDomain.compContFun g f)
    let unitComp : OrderedDomain.ContFunCarrier D FG.model.domain :=
      OrderedDomain.compContFun FG.unit (OrderedDomain.compContFun g f)
    have hMapComp : mapComp = FD.extension FG.model unitComp := by
      apply FD.extension_unique
      intro d
      simpa [mapComp, unitComp, OrderedDomain.compContFun, Chapter3.ContFun.comp] using
        F.map_unit hDdcpo hD hGdcpo hG (OrderedDomain.compContFun g f) d
    have hComposite : DcpoAlgebraHom.comp mapG mapF = FD.extension FG.model unitComp := by
      apply FD.extension_unique
      intro d
      change mapG.toFun (mapF.toFun (FD.unit d)) = FG.unit (g (f d))
      rw [show mapF.toFun (FD.unit d) = (F.obj E hEdcpo hE).unit (f d) by
        simpa [mapF, FD] using F.map_unit hDdcpo hD hEdcpo hE f d]
      simpa [mapG, FG] using F.map_unit hEdcpo hE hGdcpo hG g (f d)
    calc
      mapComp.toFun x = (FD.extension FG.model unitComp).toFun x := by rw [hMapComp]
      _ = (DcpoAlgebraHom.comp mapG mapF).toFun x := by rw [hComposite]
      _ = mapG.toFun (mapF.toFun x) := rfl
  · intro D E hDdcpo hD hEdcpo hE f g hfg y
    let FD := F.obj D hDdcpo hD
    let FE := F.obj E hEdcpo hE
    let mapF := F.map hDdcpo hD hEdcpo hE f
    let mapG := F.map hDdcpo hD hEdcpo hE g
    let unitG : OrderedDomain.ContFunCarrier D FE.model.domain :=
      OrderedDomain.compContFun FE.unit g
    have hMapF : mapF = FD.extension FE.model unitG := by
      apply FD.extension_unique
      intro d
      change mapF.toFun (FD.unit d) = FE.unit (g d)
      rw [show mapF.toFun (FD.unit d) = FE.unit (f d) by
        simpa [mapF, FD, FE] using F.map_unit hDdcpo hD hEdcpo hE f d]
      rw [hfg d]
    have hMapG : mapG = FD.extension FE.model unitG := by
      apply FD.extension_unique
      intro d
      simpa [mapG, FD, FE, unitG, OrderedDomain.compContFun, Chapter3.ContFun.comp] using
        F.map_unit hDdcpo hD hEdcpo hE g d
    calc
      mapF.toFun y = (FD.extension FE.model unitG).toFun y := by rw [hMapF]
      _ = mapG.toFun y := by rw [hMapG]
  · intro D E hDdcpo hD hEdcpo hE
    let FD := F.obj D hDdcpo hD
    let FE := F.obj E hEdcpo hE
    let postUnit : OrderedDomain.ContFunCarrier D E →
        OrderedDomain.ContFunCarrier D FE.model.domain :=
      fun f => OrderedDomain.compContFun FE.unit f
    let extend : OrderedDomain.ContFunCarrier D FE.model.domain →
        OrderedDomain.ContFunCarrier FD.model.domain FE.model.domain :=
      fun g => DcpoAlgebraHom.toContFun (FD.extension FE.model g)
    have hPost : Chapter3.ScottContinuous postUnit := by
      exact contFun_postcompose_scottContinuous hEdcpo FE.unit
    have hExtend : Chapter3.ScottContinuous extend := by
      exact FD.extension_map_scott_continuous FE.model
    have hComp : Chapter3.ScottContinuous (fun f => extend (postUnit f)) :=
      hExtend.comp hPost
    have hExtension :
        Chapter3.ScottContinuous
          (fun f : OrderedDomain.ContFunCarrier D E =>
            DcpoAlgebraHom.toContFun (FD.extension FE.model (postUnit f))) := by
      simpa only [extend] using hComp
    have hfun :
        (fun f : OrderedDomain.ContFunCarrier D E =>
          DcpoAlgebraHom.toContFun (F.map hDdcpo hD hEdcpo hE f)) =
        (fun f : OrderedDomain.ContFunCarrier D E =>
          DcpoAlgebraHom.toContFun (FD.extension FE.model (postUnit f))) := by
      funext f
      apply congrArg DcpoAlgebraHom.toContFun
      apply FD.extension_unique
      intro d
      simpa [FD, FE, postUnit, OrderedDomain.compContFun, Chapter3.ContFun.comp] using
        F.map_unit hDdcpo hD hEdcpo hE f d
    rw [hfun]
    exact hExtension

/-- A free algebra whose carrier is algebraic. -/
structure FreeAlgebraicDomainAlgebraForTheory
    {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) (D : OrderedDomain.{w})
    extends FreeDcpoAlgebraForTheory T D where
  algebraic_domain : Chapter3.IsAlgebraicDomain model.domain.carrier

/-- Object/morphism-action data for the free algebraic-domain algebra
construction, including the unit square for the induced map on free algebras.
It is not yet a categorical functor or adjunction: identity/composition,
naturality, and hom-set equivalence laws remain interface debt. -/
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

The textbook derives this from reflexivity of approximation on the compact basis.
The current ideal-completion package does not yet transport that reflexivity to
the bundled free-algebra functor; ten distinct strategies have been exhausted. -/
theorem theorem_6_1_10_free_algebraic_domain_algebras_exist
    {Sig : Signature.{u, v}} {Var : Type w} (T : Theory Sig Var) :
    Nonempty (FreeAlgebraicDomainAlgebraFunctor T) := by
  sorry

/-- A map reflects the order of its domain. -/
def OrderReflecting {D E : OrderedDomain.{u}} (f : D.carrier → E.carrier) : Prop :=
  ∀ ⦃x y : D.carrier⦄, f x ≤ f y → x ≤ y

/-- The non-triviality hypothesis actually used by the reverse implication of
Proposition 6.1.11: the generating dcpo contains a strict comparable pair. -/
def HasNontrivialOrder (D : OrderedDomain.{u}) : Prop :=
  ∃ lower upper : D.carrier, lower ≤ upper ∧ ¬ upper ≤ lower

/-- A model whose carrier has a genuinely non-trivial order. -/
structure NontriviallyOrderedModel {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) where
  model : Model T
  lower : model.domain.carrier
  upper : model.domain.carrier
  le_lower_upper : lower ≤ upper
  not_le_upper_lower : ¬ upper ≤ lower

/-- Proposition 6.1.11.  The canonical map `eta : D -> F(D)` is
order-reflecting iff the theory has a non-trivially ordered dcpo-algebra model.

The source's converse uses the free algebra itself as the non-trivial model, so
it implicitly requires `D` to contain a strict comparable pair.  Without this
hypothesis the fixed-`D` statement is false for a one-point dcpo. -/
theorem prop_6_1_11_unit_order_reflection_criterion
    {Sig : Signature.{u, v}} {Var : Type w}
    {T : Theory Sig Var} {D : OrderedDomain.{w}}
    (F : FreeDcpoAlgebraForTheory T D) (hDnontrivial : HasNontrivialOrder D) :
    OrderReflecting F.unit ↔ Nonempty (NontriviallyOrderedModel T) := by
  constructor
  · intro hreflect
    rcases hDnontrivial with ⟨lower, upper, hle, hnle⟩
    refine ⟨{
      model := F.model
      lower := F.unit lower
      upper := F.unit upper
      le_lower_upper := F.unit.continuous.1 hle
      not_le_upper_lower := ?_
    }⟩
    intro hreverse
    exact hnle (hreflect hreverse)
  · rintro ⟨A⟩
    intro x y hunit
    by_contra hxy
    classical
    let separate : D.carrier → A.model.domain.carrier := fun d =>
      if d ≤ y then A.lower else A.upper
    have hseparate : Chapter3.ScottContinuous separate := by
      constructor
      · intro d e hde
        by_cases hey : e ≤ y
        · have hdy : d ≤ y := le_trans hde hey
          simp [separate, hdy, hey]
        · by_cases hdy : d ≤ y
          · simpa [separate, hdy, hey] using A.le_lower_upper
          · simp [separate, hdy, hey]
      · intro S s hS hs
        by_cases hsy : s ≤ y
        · have hAll : ∀ d ∈ S, d ≤ y := by
            intro d hd
            exact le_trans (hs.1 hd) hsy
          have himage : separate '' S = ({A.lower} : Set A.model.domain.carrier) := by
            ext z
            constructor
            · intro hz
              rcases hz with ⟨d, hd, rfl⟩
              simp [separate, hAll d hd]
            · intro hz
              have hzEq : z = A.lower := by simpa using hz
              rcases hS.1 with ⟨d, hd⟩
              exact ⟨d, hd, by simpa [separate, hAll d hd] using hzEq.symm⟩
          simpa [separate, hsy, himage] using Chapter2.isSup_singleton A.lower
        · have hexists : ∃ d ∈ S, ¬ d ≤ y := by
            by_contra hnone
            apply hsy
            exact hs.2 y (by
              intro d hd
              by_contra hdny
              exact hnone ⟨d, hd, hdny⟩)
          rcases hexists with ⟨d₀, hd₀, hd₀y⟩
          have hUpper : Chapter3.IsUpperBound (separate '' S) A.upper := by
            intro z hz
            rcases hz with ⟨d, _hd, rfl⟩
            by_cases hdy : d ≤ y
            · simpa [separate, hdy] using A.le_lower_upper
            · simp [separate, hdy]
          have hMem : A.upper ∈ separate '' S := by
            exact ⟨d₀, hd₀, by simp [separate, hd₀y]⟩
          have hSup : Chapter3.IsSup (separate '' S) A.upper := by
            constructor
            · exact hUpper
            · intro z hz
              exact hz hMem
          simpa [separate, hsy] using hSup
    let g : OrderedDomain.ContFunCarrier D A.model.domain := {
      toFun := separate
      continuous := hseparate
    }
    have hmono := (F.extension A.model g).continuous.1 hunit
    have hx : separate x = A.upper := by simp [separate, hxy]
    have hy : separate y = A.lower := by simp [separate]
    have hextx := F.extension_unit A.model g x
    have hexty := F.extension_unit A.model g y
    apply A.not_le_upper_lower
    simpa [g, hx, hy, hextx, hexty] using hmono

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

/-- Object/morphism-action data for the free strict dcpo-algebra construction.
Functor laws and the left-adjoint package are not yet encoded. -/
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

/-- Object/morphism-action data for the free strict continuous-domain algebra
construction. Functor laws and the left-adjoint package are not yet encoded. -/
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

/-- Object/morphism-action data for the free strict algebraic-domain algebra
construction. Functor laws and the left-adjoint package are not yet encoded. -/
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

The source explains both the pointed-dcpo Adjoint Functor Theorem argument and
the additional syntactic axiom used for pointed continuous/algebraic domains.
The three functorial constructions remain an `automation_exhausted` boundary
after ten source-guided strategies; the proof is not omitted by the book. -/
theorem theorem_6_1_13_free_strict_algebras_exist
    {Sig : Signature.{u, v}} {Var : Type w} (T : Theory Sig Var) :
    Nonempty (FreeStrictAlgebraFunctor T) ∧
      Nonempty (FreeStrictContinuousDomainAlgebraFunctor T) ∧
        Nonempty (FreeStrictAlgebraicDomainAlgebraFunctor T) := by
  sorry

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

The textbook states this proposition without a proof.  The finite-target case is
proved above, while the extension along a bifinite bilimit is therefore retained
as a genuine `auto_inferred_book_omission` boundary. -/
theorem prop_6_1_14_finite_preservation_bifinite
    {Sig : Signature.{u, v}} {Var : Type w} {T : Theory Sig Var}
    (F : FreeStrictAlgebraFunctor T)
    (hfinite : FreeFunctorPreservesFinitePointed F) :
    FreeFunctorRestrictsToBifinite F := by
  admit

end Chapter6
end AbramskyJung

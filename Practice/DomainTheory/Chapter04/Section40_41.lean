import Practice.DomainTheory.Chapter04

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Chapter 4, Sections 4.0-4.1

Step functions and the first lattice-like domain classes used in Chapter 4.

Some numbered results in this file are direct Lean proofs, while the ideal
completion and function-space clauses are registered as visible proof debt with
auxiliary support packages. See `formalization_status.md` for the item-by-item
semantic-strength audit.
-/

universe u v

namespace AbramskyJung
namespace Chapter4

/-- Definition 4.0.1, general form. PDF text: "we will use `(O ↘ e)` for the
function which maps the Scott-open set `O` to `e` and everything else to `⊥`." -/
noncomputable def OpenStepFunction
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot E]
    (O : Set D) (e : E) : D → E := by
  classical
  exact fun x => if x ∈ O then e else ⊥

/-- Definition 4.0.1, general open-set step notation. PDF text: "`(O ↘ e)`"
maps a Scott-open set `O` to `e` and everything else to bottom. -/
noncomputable abbrev def_4_0_1_open_step_functions
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot E]
    (O : Set D) (e : E) : D → E :=
  OpenStepFunction O e

/-- Definition 4.0.1. PDF text: for dcpos `D` and `E`, where `E` has a least
element, and for `d ∈ D`, `e ∈ E`, the step function `(d ↘ e) : D → E` maps
`x` to `e` if `x ∈ Int(↑d)` and to `⊥_E` otherwise. -/
noncomputable def StepFunction
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot E]
    (d : D) (e : E) : D → E := by
  classical
  exact fun x =>
    if Chapter2.ScottInteriorMem (Chapter2.upperClosure ({d} : Set D)) x then e else ⊥

/-- Definition 4.0.1: principal step functions `(d ↘ e)`, using the Scott
interior of the principal upper set of `d`. -/
noncomputable abbrev def_4_0_1_step_functions
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot E]
    (d : D) (e : E) : D → E :=
  StepFunction d e

/-- General open-set step functions are monotone when the selected set is Scott-open. -/
theorem openStepFunction_monotone
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot E]
    {O : Set D} (hO : Chapter2.ScottOpen O) (e : E) :
    Monotone (OpenStepFunction O e) := by
  classical
  intro x y hxy
  by_cases hx : x ∈ O
  · have hy : y ∈ O := Chapter2.scottOpen_upper hO hx hxy
    simp [OpenStepFunction, hx, hy]
  · simp [OpenStepFunction, hx]

/-- Proposition 4.0.2(1), general open-set form: every open-set step function is
Scott-continuous. -/
theorem openStepFunction_scottContinuous
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot E]
    {O : Set D} (hO : Chapter2.ScottOpen O) (e : E) :
    Chapter3.ScottContinuous (OpenStepFunction O e) := by
  classical
  constructor
  · exact openStepFunction_monotone hO e
  · intro A x hA hx
    constructor
    · intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      exact openStepFunction_monotone hO e (hx.1 ha)
    · intro y hy
      by_cases hxO : x ∈ O
      · have hIntersects : ∃ a ∈ A, a ∈ O := by
          by_contra hnone
          have hAcompl : A ⊆ Oᶜ := by
            intro a ha haO
            exact hnone ⟨a, ha, haO⟩
          have hxCompl : x ∈ Oᶜ := hO.2 hA hAcompl hx
          exact hxCompl hxO
        rcases hIntersects with ⟨a, ha, haO⟩
        have he_mem : e ∈ OpenStepFunction O e '' A := by
          exact ⟨a, ha, by simp [OpenStepFunction, haO]⟩
        have hey : e ≤ y := hy he_mem
        simpa [OpenStepFunction, hxO] using hey
      · have hbot : (⊥ : E) ≤ y := bot_le
        simpa [OpenStepFunction, hxO] using hbot

/-- Step functions are monotone; this is the order-theoretic core of Proposition 4.0.2. -/
theorem stepFunction_monotone
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot E]
    (d : D) (e : E) : Monotone (StepFunction d e) := by
  classical
  intro x y hxy
  by_cases hx : Chapter2.ScottInteriorMem (Chapter2.upperClosure ({d} : Set D)) x
  · have hy : Chapter2.ScottInteriorMem (Chapter2.upperClosure ({d} : Set D)) y := by
      rcases hx with ⟨O, hO, hsub, hxO⟩
      exact ⟨O, hO, hsub, Chapter2.scottOpen_upper hO hxO hxy⟩
    simp [StepFunction, hx, hy]
  · simp [StepFunction, hx]

/-- Proposition 4.0.2(1). PDF text: "Step functions are Scott-continuous."

The approximation and supremum-of-step-functions clauses are represented below
by `StepFunctionSupremumStatement`. -/
theorem prop_4_0_2_step_functions
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot E]
    (d : D) (e : E) : Chapter3.ScottContinuous (StepFunction d e) := by
  classical
  constructor
  · exact stepFunction_monotone d e
  · intro A x hA hx
    constructor
    · intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      exact stepFunction_monotone d e (hx.1 ha)
    · intro y hy
      by_cases hxInterior :
          Chapter2.ScottInteriorMem (Chapter2.upperClosure ({d} : Set D)) x
      · rcases hxInterior with ⟨O, hO, hOsub, hxO⟩
        have hxInteriorStep :
            Chapter2.ScottInteriorMem (Chapter2.upperClosure ({d} : Set D)) x :=
          ⟨O, hO, hOsub, hxO⟩
        have hIntersects : ∃ a ∈ A, a ∈ O := by
          by_contra hnone
          have hAcompl : A ⊆ Oᶜ := by
            intro a ha haO
            exact hnone ⟨a, ha, haO⟩
          have hxCompl : x ∈ Oᶜ := hO.2 hA hAcompl hx
          exact hxCompl hxO
        rcases hIntersects with ⟨a, ha, haO⟩
        have haInterior :
            Chapter2.ScottInteriorMem (Chapter2.upperClosure ({d} : Set D)) a :=
          ⟨O, hO, hOsub, haO⟩
        have he_mem :
            e ∈ StepFunction d e '' A := by
          exact ⟨a, ha, by simp [StepFunction, haInterior]⟩
        have hey : e ≤ y := hy he_mem
        simpa [StepFunction, hxInteriorStep] using hey
      · have hbot : (⊥ : E) ≤ y := bot_le
        simpa [StepFunction, hxInterior] using hbot

/-- Bundled principal step function as a Scott-continuous map. -/
noncomputable def StepFunctionContFun
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot E]
    (d : D) (e : E) : Chapter3.ContFun D E where
  toFun := StepFunction d e
  continuous := prop_4_0_2_step_functions d e

/-- A step function is below a continuous map as soon as its non-bottom value is
below the map at the step's base point. -/
theorem stepFunctionContFun_le_of_value_le
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot E]
    {g : Chapter3.ContFun D E} {d : D} {e : E} (he : e ≤ g d) :
    StepFunctionContFun d e ≤ g := by
  classical
  intro x
  by_cases hxInterior :
      Chapter2.ScottInteriorMem (Chapter2.upperClosure ({d} : Set D)) x
  · have hxInteriorStep :
        Chapter2.ScottInteriorMem (Chapter2.upperClosure ({d} : Set D)) x :=
      hxInterior
    rcases hxInterior with ⟨O, hO, hOsub, hxO⟩
    rcases hOsub hxO with ⟨z, hz, hzx⟩
    have hzd : z = d := by simpa using hz
    have hdx : d ≤ x := by simpa [hzd] using hzx
    have heg : e ≤ g x := le_trans he (g.continuous.1 hdx)
    simpa [StepFunctionContFun, StepFunction, hxInteriorStep] using heg
  · have hbot : (⊥ : E) ≤ g x := bot_le
    simpa [StepFunctionContFun, StepFunction, hxInterior] using hbot

/-- Chapter 3 uses the strong basis predicate; Chapter 2's topology and
interpolation lemmas use the raw basis predicate. -/
theorem chapter3Continuous_to_chapter2Continuous
    {D : Type u} [Preorder D] (hD : Chapter3.IsContinuousDomain D) :
    Chapter2.IsContinuousDomain D := by
  rcases hD with ⟨B, hB⟩
  exact ⟨B, Chapter2.basis_to_raw hB⟩

/-- If `y` approximates `d`, then the step function based at `y` takes value
`e` at `d`. -/
theorem stepFunctionContFun_apply_of_wayBelow
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot E]
    (hD : Chapter3.IsContinuousDomain D) {y d : D} (hyd : y ≪ d) (e : E) :
    StepFunctionContFun y e d = e := by
  classical
  have hDraw : Chapter2.IsContinuousDomain D :=
    chapter3Continuous_to_chapter2Continuous hD
  have hInterior :
      Chapter2.ScottInteriorMem (Chapter2.upperClosure ({y} : Set D)) d :=
    (Chapter2.prop_2_3_5_wayBelow_iff_scottInterior hDraw).mp hyd
  simp [StepFunctionContFun, StepFunction, hInterior]

/-- The principal step-function approximants of a continuous function. -/
def StepFunctionApproximationSet
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot E]
    (f : Chapter3.ContFun D E) : Set (Chapter3.ContFun D E) :=
  {g : Chapter3.ContFun D E |
    ∃ d : D, ∃ e : E, e ≪ f d ∧ g = StepFunctionContFun d e}

/-- Proposition 4.0.2(2)-(3), faithful statement package. PDF text: if `e`
approximates `f d`, then `(d ↘ e)` approximates `f`; if, in addition, `D` and
`E` are continuous, then `f` is a supremum of step functions.

The PDF explicitly notes after the proof that this supremum need not be
directed.  Directedness is therefore not part of this statement package. -/
structure StepFunctionSupremumStatement
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot E] : Prop where
  step_approximates :
    Chapter3.IsDcpo D → Chapter3.IsDcpo E →
    ∀ (f : Chapter3.ContFun D E) (d : D) (e : E),
      e ≪ f d → StepFunctionContFun d e ≪ f
  continuous_sup_of_steps :
    Chapter3.IsDcpo D → Chapter3.IsDcpo E →
    Chapter3.IsContinuousDomain D → Chapter3.IsContinuousDomain E →
      ∀ f : Chapter3.ContFun D E,
        Chapter3.IsSup (StepFunctionApproximationSet f) f

/-- Strengthened step-function approximation data used later for function-space
continuity.  This adds directedness of the step approximants; that directedness
is stronger than Proposition 4.0.2 itself and is not claimed by the PDF's
statement of 4.0.2. -/
structure StepFunctionApproximationData
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot E] : Prop where
  step_approximates :
    Chapter3.IsDcpo D → Chapter3.IsDcpo E →
    ∀ (f : Chapter3.ContFun D E) (d : D) (e : E),
      e ≪ f d → StepFunctionContFun d e ≪ f
  step_approximants_directed :
    Chapter3.IsDcpo D → Chapter3.IsDcpo E →
    Chapter3.IsContinuousDomain D → Chapter3.IsContinuousDomain E →
      ∀ f : Chapter3.ContFun D E,
        Chapter3.DirectedSet (StepFunctionApproximationSet f)
  continuous_sup_of_steps :
    Chapter3.IsDcpo D → Chapter3.IsDcpo E →
    Chapter3.IsContinuousDomain D → Chapter3.IsContinuousDomain E →
      ∀ f : Chapter3.ContFun D E,
        Chapter3.IsSup (StepFunctionApproximationSet f) f

/-- The strengthened directed approximation data contains the faithful
Proposition 4.0.2(2)-(3) supremum data. -/
def StepFunctionApproximationData.toSupremumStatement
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot E]
    (h : StepFunctionApproximationData D E) :
    StepFunctionSupremumStatement D E where
  step_approximates := h.step_approximates
  continuous_sup_of_steps := h.continuous_sup_of_steps

/-- Proposition 4.0.2(2)-(3).  PDF text: if `e` approximates `f d`, then
`(d ↘ e)` approximates `f`; if, in addition, `D` and `E` are continuous, then
`f` is a supremum of step functions.  The PDF note says this supremum need not
be directed, so directedness is intentionally absent from this numbered
theorem. -/
theorem prop_4_0_2_step_function_approximation_and_supremum
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot E] :
    StepFunctionSupremumStatement D E := by
  classical
  refine ⟨?_, ?_⟩
  · intro _hD hE f d e he A s hA hs hfs
    have hEvalSup :
        Chapter3.IsSup ((fun g : Chapter3.ContFun D E => g d) '' A) (s d) :=
      (Chapter3.ContFun.eval_scottContinuous hE d).2 hA hs
    rcases he (Chapter3.ContFun.eval_directed hA d) hEvalSup (hfs d) with
      ⟨ed, hed, heed⟩
    rcases hed with ⟨g, hgA, rfl⟩
    exact ⟨g, hgA, stepFunctionContFun_le_of_value_le heed⟩
  · intro _hD _hE hDcont hEcont f
    constructor
    · intro g hg
      rcases hg with ⟨d, e, he, rfl⟩
      exact stepFunctionContFun_le_of_value_le (Chapter3.wayBelow_le he)
    · intro g hg d
      have hDraw : Chapter2.IsContinuousDomain D :=
        chapter3Continuous_to_chapter2Continuous hDcont
      have hEraw : Chapter2.IsContinuousDomain E :=
        chapter3Continuous_to_chapter2Continuous hEcont
      have hDomainDir : Chapter3.DirectedSet (Chapter2.wayBelowLower d) :=
        Chapter2.continuous_wayBelowLower_directed hDraw d
      have hDomainSup : Chapter3.IsSup (Chapter2.wayBelowLower d) d :=
        Chapter2.continuous_wayBelowLower_isSup hDraw d
      have hImageDir : Chapter3.DirectedSet (f '' Chapter2.wayBelowLower d) :=
        Chapter2.DirectedSet.image f.continuous.1 hDomainDir
      have hImageSup : Chapter3.IsSup (f '' Chapter2.wayBelowLower d) (f d) :=
        f.continuous.2 hDomainDir hDomainSup
      have hValueSup : Chapter3.IsSup (Chapter2.wayBelowLower (f d)) (f d) :=
        Chapter2.continuous_wayBelowLower_isSup hEraw (f d)
      refine hValueSup.2 (g d) ?_
      intro e he
      rcases Chapter2.cor_2_2_16_wayBelow_directed_sup hEraw hImageDir hImageSup he with
        ⟨fy, hfy, hefy⟩
      rcases hfy with ⟨y, hyd, rfl⟩
      have hStepMem : StepFunctionContFun y e ∈ StepFunctionApproximationSet f :=
        ⟨y, e, hefy, rfl⟩
      have hStepLe : StepFunctionContFun y e ≤ g := hg hStepMem
      have hStepAt : StepFunctionContFun y e d = e :=
        stepFunctionContFun_apply_of_wayBelow hDcont hyd e
      simpa [hStepAt] using hStepLe d

/-- Compatibility projection for clients that use Proposition 4.0.2 as the pair
of approximation and supremum clauses. -/
theorem prop_4_0_2_step_function_approximation_and_supremum_fields
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot E] :
    (Chapter3.IsDcpo D → Chapter3.IsDcpo E →
      ∀ (f : Chapter3.ContFun D E) (d : D) (e : E),
      e ≪ f d → StepFunctionContFun d e ≪ f) ∧
      (Chapter3.IsDcpo D → Chapter3.IsDcpo E →
        Chapter3.IsContinuousDomain D → Chapter3.IsContinuousDomain E →
        ∀ f : Chapter3.ContFun D E,
          Chapter3.IsSup (StepFunctionApproximationSet f) f) := by
  let h := (prop_4_0_2_step_function_approximation_and_supremum (D := D) (E := E))
  exact ⟨h.step_approximates, h.continuous_sup_of_steps⟩

/-- Proposition 4.0.2, all three clauses in one book-facing theorem. -/
theorem prop_4_0_2_step_functions_full
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot E] :
    (∀ d : D, ∀ e : E, Chapter3.ScottContinuous (StepFunction d e)) ∧
      StepFunctionSupremumStatement D E := by
  exact ⟨fun d e => prop_4_0_2_step_functions d e,
    prop_4_0_2_step_function_approximation_and_supremum⟩

/-- Definition 4.1.1 ambient condition: the PDF defines L-domains,
bc-domains, and continuous lattices as pointed continuous domains. -/
def HasBottom (D : OrderedDomain.{u}) : Prop :=
  ∃ bot : D.carrier, ∀ x : D.carrier, bot ≤ x

/-- Definition 4.1.1(1), the source formulation by binary suprema inside a
principal ideal. -/
def HasPrincipalBinarySuprema (D : OrderedDomain.{u}) : Prop :=
  ∀ e e₁ e₂ : D.carrier, e₁ ≤ e → e₂ ≤ e →
    ∃ s : D.carrier,
      Chapter3.IsSup ({x : D.carrier | x = e₁ ∨ x = e₂}) s ∧ s ≤ e

/-- Definition 4.1.1(2), the source formulation by suprema of bounded pairs. -/
def HasBoundedBinarySuprema (D : OrderedDomain.{u}) : Prop :=
  ∀ e₁ e₂ : D.carrier,
    (∃ e : D.carrier, e₁ ≤ e ∧ e₂ ≤ e) →
      ∃ s : D.carrier, Chapter3.IsSup ({x : D.carrier | x = e₁ ∨ x = e₂}) s

/-- Definition 4.1.1(3), the source formulation by suprema of all pairs. -/
def HasBinarySuprema (D : OrderedDomain.{u}) : Prop :=
  ∀ e₁ e₂ : D.carrier,
    ∃ s : D.carrier, Chapter3.IsSup ({x : D.carrier | x = e₁ ∨ x = e₂}) s

/-- Definition 4.1.1(1), source-facing L-domain predicate. -/
def IsLDomainByBinarySuprema (D : OrderedDomain.{u}) : Prop :=
  HasBottom D ∧ Chapter3.IsContinuousDomain D.carrier ∧ HasPrincipalBinarySuprema D

/-- Definition 4.1.1(2), source-facing bounded-complete-domain predicate. -/
def IsBcDomainByBinarySuprema (D : OrderedDomain.{u}) : Prop :=
  HasBottom D ∧ Chapter3.IsContinuousDomain D.carrier ∧ HasBoundedBinarySuprema D

/-- Definition 4.1.1(3), source-facing continuous-lattice predicate. -/
def IsContinuousLatticeDomainByBinarySuprema (D : OrderedDomain.{u}) : Prop :=
  HasBottom D ∧ Chapter3.IsContinuousDomain D.carrier ∧ HasBinarySuprema D

/-- Nonempty subsets contained in a principal ideal have infima. -/
def HasPrincipalLowerInfima (D : OrderedDomain.{u}) : Prop :=
  ∀ x : D.carrier, ∀ A : Set D.carrier,
    A.Nonempty → A ⊆ {y : D.carrier | y ≤ x} → ∃ i : D.carrier, Chapter3.IsInf A i

/-- Nonempty subsets have infima. -/
def HasNonemptyInfima (D : OrderedDomain.{u}) : Prop :=
  ∀ A : Set D.carrier, A.Nonempty → ∃ i : D.carrier, Chapter3.IsInf A i

/-- Arbitrary subsets have infima. -/
def HasAllInfima (D : OrderedDomain.{u}) : Prop :=
  ∀ A : Set D.carrier, ∃ i : D.carrier, Chapter3.IsInf A i

/-- Definition 4.1.1, represented via Proposition 4.1.2. PDF text: an
L-domain is a pointed continuous domain where each pair bounded by some `e`
has a supremum in `↓e`.  Proposition 4.1.2 gives the equivalent infimum form
used here: bounded nonempty subsets have infima. -/
def IsLDomain (D : OrderedDomain.{u}) : Prop :=
  HasBottom D ∧ Chapter3.IsContinuousDomain D.carrier ∧ HasPrincipalLowerInfima D

/-- Definition 4.1.1, represented via Proposition 4.1.2. PDF text: a
bounded-complete domain, or bc-domain, is a pointed continuous domain where
each bounded pair has a supremum.  Proposition 4.1.2 gives the equivalent
infimum form used here: all nonempty subsets have infima. -/
def IsBcDomain (D : OrderedDomain.{u}) : Prop :=
  HasBottom D ∧ Chapter3.IsContinuousDomain D.carrier ∧ HasNonemptyInfima D

/-- Definition 4.1.1, represented via Proposition 4.1.2. PDF text: repeated for
comparison, a continuous lattice is a pointed continuous domain where each pair
has a supremum.  Proposition 4.1.2 gives the equivalent infimum form used here:
arbitrary subsets have infima, representing the continuous-lattice objects of
`CONT⊥`. -/
def IsContinuousLatticeDomain (D : OrderedDomain.{u}) : Prop :=
  HasBottom D ∧ Chapter3.IsContinuousDomain D.carrier ∧ HasAllInfima D

/-- Definition 4.1.1 aggregate predicate for the three lattice-like object
classes.  The full subcategory names `L`, `BC`, `LAT`, `aL`, `aBC`, and `aLAT`
are represented below as `DomainClass` predicates. -/
def def_4_1_1_lattice_like_domain_classes (D : OrderedDomain.{u}) : Prop :=
  IsLDomain D ∨ IsBcDomain D ∨ IsContinuousLatticeDomain D

/-- Proposition 4.1.2. PDF text: "Let `D` be a pointed continuous domain. Then
`D` is an L-domain, a bc-domain, or a continuous lattice if and only if it has
infima for bounded non-empty, non-empty, or arbitrary subsets, respectively."

Current Lean spelling: the object-class predicates above are deliberately
defined in this equivalent infimum form, so the theorem is definitional. -/
theorem prop_4_1_2_lattice_like_infimum_characterizations (D : OrderedDomain.{u}) :
    (IsLDomain D ↔
      HasBottom D ∧ Chapter3.IsContinuousDomain D.carrier ∧ HasPrincipalLowerInfima D) ∧
    (IsBcDomain D ↔
      HasBottom D ∧ Chapter3.IsContinuousDomain D.carrier ∧ HasNonemptyInfima D) ∧
    (IsContinuousLatticeDomain D ↔
      HasBottom D ∧ Chapter3.IsContinuousDomain D.carrier ∧ HasAllInfima D) := by
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Proposition 4.1.2 with Definition 4.1.1 encoded independently on the left.
The book omits the proof, so this exact bridge remains visible proof debt. -/
theorem prop_4_1_2_source_infimum_characterizations (D : OrderedDomain.{u}) :
    (IsLDomainByBinarySuprema D ↔ IsLDomain D) ∧
      (IsBcDomainByBinarySuprema D ↔ IsBcDomain D) ∧
        (IsContinuousLatticeDomainByBinarySuprema D ↔ IsContinuousLatticeDomain D) := by
  admit

/-- The Chapter 3 bilimit carrier, viewed as a Chapter 4 ordered-domain object. -/
def BilimitOrderedDomain
    (D : Nat → OrderedDomain.{u})
    (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier)) : OrderedDomain.{u} where
  carrier := Chapter3.Bilimit S
  preorder := inferInstance

/-- Proposition 4.1.3, retract clause. PDF text: "Retracts and bilimits of
L-domains (bc-domains, continuous lattices) are again L-domains (bc-domains,
continuous lattices)."

Current Lean spelling: this legacy-named theorem proves only the retract half,
using continuous section-retraction pairs.  The bilimit half is proved below as
`prop_4_1_3_bilimits_lattice_like`. -/
theorem prop_4_1_3_retracts_bilimits_lattice_like
    {D E : OrderedDomain.{u}}
    (sr : Chapter3.ContinuousSectionRetractionPair D.carrier E.carrier) :
    (IsLDomain E → IsLDomain D) ∧
      (IsBcDomain E → IsBcDomain D) ∧
      (IsContinuousLatticeDomain E → IsContinuousLatticeDomain D) := by
  constructor
  · intro hE
    rcases hE with ⟨hbotE, hcontE, hinfE⟩
    constructor
    · rcases hbotE with ⟨botE, hbotE⟩
      exact ⟨sr.r botE, by
        intro x
        calc
          sr.r botE ≤ sr.r (sr.s x) := sr.monotone_r (hbotE (sr.s x))
          _ = x := sr.retract x⟩
    constructor
    · exact Chapter3.theorem_3_1_4_retract_continuous_domain_basis sr hcontE
    · intro x A hAne hAprincipal
      have hImageNonempty : (sr.s '' A).Nonempty := hAne.image sr.s
      have hImagePrincipal : sr.s '' A ⊆ {y : E.carrier | y ≤ sr.s x} := by
        intro y hy
        rcases hy with ⟨a, ha, rfl⟩
        exact sr.monotone_s (hAprincipal ha)
      rcases hinfE (sr.s x) (sr.s '' A) hImageNonempty hImagePrincipal with ⟨q, hq⟩
      exact ⟨sr.r q, sr.toSectionRetractionPair.isInf_of_section_image_isInf hq⟩
  constructor
  · intro hE
    rcases hE with ⟨hbotE, hcontE, hinfE⟩
    constructor
    · rcases hbotE with ⟨botE, hbotE⟩
      exact ⟨sr.r botE, by
        intro x
        calc
          sr.r botE ≤ sr.r (sr.s x) := sr.monotone_r (hbotE (sr.s x))
          _ = x := sr.retract x⟩
    constructor
    · exact Chapter3.theorem_3_1_4_retract_continuous_domain_basis sr hcontE
    · intro A hAne
      have hImageNonempty : (sr.s '' A).Nonempty := hAne.image sr.s
      rcases hinfE (sr.s '' A) hImageNonempty with ⟨q, hq⟩
      exact ⟨sr.r q, sr.toSectionRetractionPair.isInf_of_section_image_isInf hq⟩
  · intro hE
    rcases hE with ⟨hbotE, hcontE, hinfE⟩
    constructor
    · rcases hbotE with ⟨botE, hbotE⟩
      exact ⟨sr.r botE, by
        intro x
        calc
          sr.r botE ≤ sr.r (sr.s x) := sr.monotone_r (hbotE (sr.s x))
          _ = x := sr.retract x⟩
    constructor
    · exact Chapter3.theorem_3_1_4_retract_continuous_domain_basis sr hcontE
    · intro A
      rcases hinfE (sr.s '' A) with ⟨q, hq⟩
      exact ⟨sr.r q, sr.toSectionRetractionPair.isInf_of_section_image_isInf hq⟩

/-- Proposition 4.1.3, bilimit support: if all stages are continuous domains,
the bilimit is continuous. This reuses the Chapter 3 bilimit-preservation
theorem and makes the dcpo/poset context explicit. -/
theorem bilimit_continuousDomain_of_stage_continuous
    (D : Nat → OrderedDomain.{u})
    (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier))
    (hDdcpo : ∀ n : Nat, Chapter3.IsDcpo (D n).carrier)
    (hantisymm : ∀ n : Nat, ∀ x y : (D n).carrier, x ≤ y → y ≤ x → x = y)
    (hContinuous : ∀ n : Nat, Chapter3.IsContinuousDomain (D n).carrier) :
    Chapter3.IsContinuousDomain (BilimitOrderedDomain D S).carrier := by
  exact (Chapter3.theorem_3_3_11_expanding_sequence_bilimit_preservation
    S hDdcpo hantisymm) hContinuous

/-- Proposition 4.1.3, bilimit support: stage bottoms assemble into a bottom
element of the bilimit. -/
noncomputable def bilimitBottom
    (D : Nat → OrderedDomain.{u})
    (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier))
    (hbot : ∀ n : Nat, HasBottom (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : (D n).carrier, x ≤ y → y ≤ x → x = y) :
    Chapter3.Bilimit S := by
  classical
  refine ⟨fun n => Classical.choose (hbot n), ?_⟩
  intro n m hnm
  apply hantisymm n
  · exact Classical.choose_spec (hbot n) (S.p hnm (Classical.choose (hbot m)))
  · have hStage :
        Classical.choose (hbot m) ≤ S.e hnm (Classical.choose (hbot n)) :=
      Classical.choose_spec (hbot m) (S.e hnm (Classical.choose (hbot n)))
    calc
      S.p hnm (Classical.choose (hbot m))
          ≤ S.p hnm (S.e hnm (Classical.choose (hbot n))) :=
            (S.continuous_p hnm).1 hStage
      _ = Classical.choose (hbot n) := S.retract hnm (Classical.choose (hbot n))

/-- Proposition 4.1.3, bilimit support: if every stage has a bottom, then the
bilimit ordered domain has a bottom. -/
theorem bilimit_hasBottom_of_stage_bottoms
    (D : Nat → OrderedDomain.{u})
    (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier))
    (hbot : ∀ n : Nat, HasBottom (D n))
    (hantisymm : ∀ n : Nat, ∀ x y : (D n).carrier, x ≤ y → y ≤ x → x = y) :
    HasBottom (BilimitOrderedDomain D S) := by
  classical
  refine ⟨bilimitBottom D S hbot hantisymm, ?_⟩
  intro x n
  exact Classical.choose_spec (hbot n) (x.1 n)

/-- The `n`-th coordinate set of a set of bilimit points. -/
def BilimitCoordinateSet
    (D : Nat → OrderedDomain.{u})
    (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier))
    (A : Set (Chapter3.Bilimit S)) (n : Nat) : Set (D n).carrier :=
  Chapter3.Bilimit.proj S n '' A

/-- Chapter 4 wrapper for Proposition 3.1.12(5): upper adjoints preserve
existing infima. This is the order-theoretic observation used in Proposition
4.1.3. -/
theorem upperAdjoint_preserves_inf_orderedDomain
    {P Q : OrderedDomain.{u}} {l : P.carrier → Q.carrier} {r : Q.carrier → P.carrier}
    (h : Chapter3.Adjunction l r) {A : Set Q.carrier} {i : Q.carrier}
    (hi : Chapter3.IsInf A i) :
    Chapter3.IsInf (r '' A) (r i) :=
  Chapter3.upper_adjoint_preserves_inf h hi

/-- Projection maps in an expanding sequence preserve existing infima, because
they are upper adjoints of the embeddings. -/
theorem expandingProjection_preserves_inf
    (D : Nat → OrderedDomain.{u})
    (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier))
    {n m : Nat} (hnm : n ≤ m)
    {A : Set (D m).carrier} {i : (D m).carrier}
    (hi : Chapter3.IsInf A i) :
    Chapter3.IsInf (S.p hnm '' A) (S.p hnm i) := by
  exact upperAdjoint_preserves_inf_orderedDomain
    (P := D n) (Q := D m) (l := S.e hnm) (r := S.p hnm)
    (by
      constructor
      intro x y
      exact (S.e_le_iff_le_p hnm x y).symm)
    hi

/-- Coordinatewise chosen infima form a bilimit point. -/
noncomputable def bilimitInf
    (D : Nat → OrderedDomain.{u})
    (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier))
    (A : Set (Chapter3.Bilimit S))
    (hcoord :
      ∀ n : Nat, ∃ i : (D n).carrier,
        Chapter3.IsInf (BilimitCoordinateSet D S A n) i)
    (hantisymm : ∀ n : Nat, ∀ x y : (D n).carrier, x ≤ y → y ≤ x → x = y) :
    Chapter3.Bilimit S := by
  classical
  refine ⟨fun n => Classical.choose (hcoord n), ?_⟩
  intro n m hnm
  let im : (D m).carrier := Classical.choose (hcoord m)
  let pinf : (D n).carrier := S.p hnm im
  have hm : Chapter3.IsInf (BilimitCoordinateSet D S A m) im :=
    Classical.choose_spec (hcoord m)
  have hn : Chapter3.IsInf (BilimitCoordinateSet D S A n) (Classical.choose (hcoord n)) :=
    Classical.choose_spec (hcoord n)
  have hpinf : Chapter3.IsInf (BilimitCoordinateSet D S A n) pinf := by
    constructor
    · intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      change pinf ≤ a.1 n
      rw [a.2 hnm]
      exact (S.continuous_p hnm).1 (hm.1 ⟨a, ha, rfl⟩)
    · intro y hy
      apply (S.e_le_iff_le_p hnm y im).1
      exact hm.2 (S.e hnm y) (by
        intro z hz
        rcases hz with ⟨a, ha, rfl⟩
        have hycoord : y ≤ Chapter3.Bilimit.proj S n a := hy ⟨a, ha, rfl⟩
        have hcompat :
            Chapter3.Bilimit.proj S n a =
              S.p hnm (Chapter3.Bilimit.proj S m a) := a.2 hnm
        have hyp : y ≤ S.p hnm (Chapter3.Bilimit.proj S m a) := by
          simpa [hcompat] using hycoord
        exact (S.e_le_iff_le_p hnm y (Chapter3.Bilimit.proj S m a)).2 hyp)
  exact hantisymm n (Classical.choose (hcoord n)) pinf
    (hpinf.2 (Classical.choose (hcoord n)) hn.1)
    (hn.2 pinf hpinf.1)

/-- The coordinatewise infimum point is an infimum in the bilimit. -/
theorem bilimitInf_isInf
    (D : Nat → OrderedDomain.{u})
    (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier))
    (A : Set (Chapter3.Bilimit S))
    (hcoord :
      ∀ n : Nat, ∃ i : (D n).carrier,
        Chapter3.IsInf (BilimitCoordinateSet D S A n) i)
    (hantisymm : ∀ n : Nat, ∀ x y : (D n).carrier, x ≤ y → y ≤ x → x = y) :
    Chapter3.IsInf A (bilimitInf D S A hcoord hantisymm) := by
  classical
  constructor
  · intro a ha n
    exact (Classical.choose_spec (hcoord n)).1 ⟨a, ha, rfl⟩
  · intro y hy n
    exact (Classical.choose_spec (hcoord n)).2 (Chapter3.Bilimit.proj S n y) (by
      intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact hy ha n)

/-- Bilimits preserve arbitrary infima when all stages have arbitrary infima. -/
theorem bilimit_hasAllInfima_of_stage_allInfima
    (D : Nat → OrderedDomain.{u})
    (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier))
    (hantisymm : ∀ n : Nat, ∀ x y : (D n).carrier, x ≤ y → y ≤ x → x = y)
    (hAllInf : ∀ n : Nat, HasAllInfima (D n)) :
    HasAllInfima (BilimitOrderedDomain D S) := by
  intro A
  let hcoord :
      ∀ n : Nat, ∃ i : (D n).carrier,
        Chapter3.IsInf (BilimitCoordinateSet D S A n) i :=
    fun n => hAllInf n (BilimitCoordinateSet D S A n)
  exact ⟨bilimitInf D S A hcoord hantisymm,
    bilimitInf_isInf D S A hcoord hantisymm⟩

/-- Bilimits preserve nonempty infima when all stages have nonempty infima. -/
theorem bilimit_hasNonemptyInfima_of_stage_nonemptyInfima
    (D : Nat → OrderedDomain.{u})
    (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier))
    (hantisymm : ∀ n : Nat, ∀ x y : (D n).carrier, x ≤ y → y ≤ x → x = y)
    (hNonemptyInf : ∀ n : Nat, HasNonemptyInfima (D n)) :
    HasNonemptyInfima (BilimitOrderedDomain D S) := by
  intro A hAne
  have hcoordNonempty :
      ∀ n : Nat, (BilimitCoordinateSet D S A n).Nonempty := by
    intro n
    rcases hAne with ⟨a, ha⟩
    exact ⟨Chapter3.Bilimit.proj S n a, ⟨a, ha, rfl⟩⟩
  let hcoord :
      ∀ n : Nat, ∃ i : (D n).carrier,
        Chapter3.IsInf (BilimitCoordinateSet D S A n) i :=
    fun n => hNonemptyInf n (BilimitCoordinateSet D S A n) (hcoordNonempty n)
  exact ⟨bilimitInf D S A hcoord hantisymm,
    bilimitInf_isInf D S A hcoord hantisymm⟩

/-- Bilimits preserve principal-ideal infima when all stages have them. -/
theorem bilimit_hasPrincipalLowerInfima_of_stage_principalLowerInfima
    (D : Nat → OrderedDomain.{u})
    (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier))
    (hantisymm : ∀ n : Nat, ∀ x y : (D n).carrier, x ≤ y → y ≤ x → x = y)
    (hPrincipalInf : ∀ n : Nat, HasPrincipalLowerInfima (D n)) :
    HasPrincipalLowerInfima (BilimitOrderedDomain D S) := by
  intro x A hAne hAprincipal
  have hcoordNonempty :
      ∀ n : Nat, (BilimitCoordinateSet D S A n).Nonempty := by
    intro n
    rcases hAne with ⟨a, ha⟩
    exact ⟨Chapter3.Bilimit.proj S n a, ⟨a, ha, rfl⟩⟩
  have hcoordPrincipal :
      ∀ n : Nat, BilimitCoordinateSet D S A n ⊆
        {y : (D n).carrier | y ≤ Chapter3.Bilimit.proj S n x} := by
    intro n y hy
    rcases hy with ⟨a, ha, rfl⟩
    exact hAprincipal ha n
  let hcoord :
      ∀ n : Nat, ∃ i : (D n).carrier,
        Chapter3.IsInf (BilimitCoordinateSet D S A n) i :=
    fun n => hPrincipalInf n (Chapter3.Bilimit.proj S n x)
      (BilimitCoordinateSet D S A n) (hcoordNonempty n) (hcoordPrincipal n)
  exact ⟨bilimitInf D S A hcoord hantisymm,
    bilimitInf_isInf D S A hcoord hantisymm⟩

/-- Proposition 4.1.3, remaining bilimit infimum data: after Chapter 3 supplies
continuity of the bilimit and stage bottoms assemble pointwise, the
lattice-like clauses still need infimum data for the bilimit carrier. -/
structure LatticeLikeBilimitInfimumData : Prop where
  l_bilimit :
    ∀ (D : Nat → OrderedDomain.{u})
      (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier)),
        (∀ n : Nat, ∀ x y : (D n).carrier, x ≤ y → y ≤ x → x = y) →
          (∀ n : Nat, IsLDomain (D n)) →
            HasPrincipalLowerInfima (BilimitOrderedDomain D S)
  bc_bilimit :
    ∀ (D : Nat → OrderedDomain.{u})
      (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier)),
        (∀ n : Nat, ∀ x y : (D n).carrier, x ≤ y → y ≤ x → x = y) →
          (∀ n : Nat, IsBcDomain (D n)) →
            HasNonemptyInfima (BilimitOrderedDomain D S)
  continuous_lattice_bilimit :
    ∀ (D : Nat → OrderedDomain.{u})
      (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier)),
        (∀ n : Nat, ∀ x y : (D n).carrier, x ≤ y → y ≤ x → x = y) →
          (∀ n : Nat, IsContinuousLatticeDomain (D n)) →
            HasAllInfima (BilimitOrderedDomain D S)

/-- Proposition 4.1.3 support: coordinatewise infima prove the remaining
bilimit infimum data for L-domains, bc-domains, and continuous lattices. -/
theorem latticeLikeBilimitInfimumData_proved :
    LatticeLikeBilimitInfimumData.{u} := by
  constructor
  · intro D S hantisymm hStages
    exact bilimit_hasPrincipalLowerInfima_of_stage_principalLowerInfima D S
      hantisymm (fun n => (hStages n).2.2)
  · intro D S hantisymm hStages
    exact bilimit_hasNonemptyInfima_of_stage_nonemptyInfima D S
      hantisymm (fun n => (hStages n).2.2)
  · intro D S hantisymm hStages
    exact bilimit_hasAllInfima_of_stage_allInfima D S
      hantisymm (fun n => (hStages n).2.2)

/-- Proposition 4.1.3, bilimit clause data: bilimits of expanding
sequences preserve the three lattice-like classes under the explicit dcpo and
poset hypotheses implicit in the book's word "domain". -/
structure LatticeLikeBilimitPreservationData : Prop where
  l_bilimit :
    ∀ (D : Nat → OrderedDomain.{u})
      (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier)),
        (∀ n : Nat, Chapter3.IsDcpo (D n).carrier) →
          (∀ n : Nat, ∀ x y : (D n).carrier, x ≤ y → y ≤ x → x = y) →
            (∀ n : Nat, IsLDomain (D n)) → IsLDomain (BilimitOrderedDomain D S)
  bc_bilimit :
    ∀ (D : Nat → OrderedDomain.{u})
      (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier)),
        (∀ n : Nat, Chapter3.IsDcpo (D n).carrier) →
          (∀ n : Nat, ∀ x y : (D n).carrier, x ≤ y → y ≤ x → x = y) →
            (∀ n : Nat, IsBcDomain (D n)) → IsBcDomain (BilimitOrderedDomain D S)
  continuous_lattice_bilimit :
    ∀ (D : Nat → OrderedDomain.{u})
      (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier)),
        (∀ n : Nat, Chapter3.IsDcpo (D n).carrier) →
          (∀ n : Nat, ∀ x y : (D n).carrier, x ≤ y → y ≤ x → x = y) →
            (∀ n : Nat, IsContinuousLatticeDomain (D n)) →
              IsContinuousLatticeDomain (BilimitOrderedDomain D S)

/-- Proposition 4.1.3 support: the remaining bilimit infimum data, together
with the Chapter 3 continuity theorem, supplies the full bilimit preservation
data. -/
theorem latticeLikeBilimitPreservationData_of_infimum
    (hInf : LatticeLikeBilimitInfimumData.{u}) :
    LatticeLikeBilimitPreservationData.{u} := by
  constructor
  · intro D S hDdcpo hantisymm hStages
    exact ⟨bilimit_hasBottom_of_stage_bottoms D S (fun n => (hStages n).1) hantisymm,
      bilimit_continuousDomain_of_stage_continuous D S hDdcpo hantisymm
        (fun n => (hStages n).2.1),
      hInf.l_bilimit D S hantisymm hStages⟩
  · intro D S hDdcpo hantisymm hStages
    exact ⟨bilimit_hasBottom_of_stage_bottoms D S (fun n => (hStages n).1) hantisymm,
      bilimit_continuousDomain_of_stage_continuous D S hDdcpo hantisymm
        (fun n => (hStages n).2.1),
      hInf.bc_bilimit D S hantisymm hStages⟩
  · intro D S hDdcpo hantisymm hStages
    exact ⟨
      bilimit_hasBottom_of_stage_bottoms D S (fun n => (hStages n).1) hantisymm,
      bilimit_continuousDomain_of_stage_continuous D S hDdcpo hantisymm
        (fun n => (hStages n).2.1),
      hInf.continuous_lattice_bilimit D S hantisymm hStages⟩

/-- Proposition 4.1.3 support: the full bilimit preservation package follows
from the coordinatewise infimum construction. -/
theorem latticeLikeBilimitPreservationData_proved :
    LatticeLikeBilimitPreservationData.{u} :=
  latticeLikeBilimitPreservationData_of_infimum
    latticeLikeBilimitInfimumData_proved

/-- Proposition 4.1.3, bilimit clause. PDF text: "Retracts and bilimits of
L-domains (bc-domains, continuous lattices) are again L-domains (bc-domains,
continuous lattices)."

Current Lean spelling: this proves the bilimit half under the explicit dcpo and
antisymmetry hypotheses used by the Chapter 3 bilimit theorem. -/
theorem prop_4_1_3_bilimits_lattice_like :
    (∀ (D : Nat → OrderedDomain.{u})
      (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier)),
        (∀ n : Nat, Chapter3.IsDcpo (D n).carrier) →
          (∀ n : Nat, ∀ x y : (D n).carrier, x ≤ y → y ≤ x → x = y) →
            (∀ n : Nat, IsLDomain (D n)) → IsLDomain (BilimitOrderedDomain D S)) ∧
      (∀ (D : Nat → OrderedDomain.{u})
        (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier)),
          (∀ n : Nat, Chapter3.IsDcpo (D n).carrier) →
            (∀ n : Nat, ∀ x y : (D n).carrier, x ≤ y → y ≤ x → x = y) →
              (∀ n : Nat, IsBcDomain (D n)) → IsBcDomain (BilimitOrderedDomain D S)) ∧
        (∀ (D : Nat → OrderedDomain.{u})
          (S : Chapter3.ExpandingSequence (fun n : Nat => (D n).carrier)),
            (∀ n : Nat, Chapter3.IsDcpo (D n).carrier) →
              (∀ n : Nat, ∀ x y : (D n).carrier, x ≤ y → y ≤ x → x = y) →
                (∀ n : Nat, IsContinuousLatticeDomain (D n)) →
                  IsContinuousLatticeDomain (BilimitOrderedDomain D S)) := by
  exact ⟨latticeLikeBilimitPreservationData_proved.l_bilimit,
    latticeLikeBilimitPreservationData_proved.bc_bilimit,
    latticeLikeBilimitPreservationData_proved.continuous_lattice_bilimit⟩

/-- Proposition 4.1.3 packaged as one declaration for the reader. The bilimit
field retains the current `Nat`-indexed expanding-sequence interface. -/
structure LatticeLikeRetractAndBilimitPreservation : Prop where
  retract :
    ∀ {D E : OrderedDomain.{u}},
      Chapter3.ContinuousSectionRetractionPair D.carrier E.carrier →
        (IsLDomain E → IsLDomain D) ∧
          (IsBcDomain E → IsBcDomain D) ∧
            (IsContinuousLatticeDomain E → IsContinuousLatticeDomain D)
  bilimit : LatticeLikeBilimitPreservationData.{u}

/-- Proposition 4.1.3, retract and bilimit clauses together. -/
theorem prop_4_1_3_retracts_and_bilimits_lattice_like :
    LatticeLikeRetractAndBilimitPreservation.{u} := by
  exact ⟨fun sr => prop_4_1_3_retracts_bilimits_lattice_like sr,
    latticeLikeBilimitPreservationData_proved⟩

/-- Proposition 4.1.4, PDF text: "Let `D` be an L-domain
(bc-domain, continuous lattice). Then `Idl(D, ⊑)` is an algebraic L-domain
(bc-domain, lattice)."  Current Lean spelling: the ideal completion is built
from an abstract basis `B`; `IdealCompletionPresentation` below records that
`B` presents the source ordered domain. -/
def IdealCompletionDomain (B : Chapter2.AbstractBasis.{u}) : OrderedDomain.{u} where
  carrier := B.Ideal
  preorder := inferInstance

/-- Proposition 4.1.4 support. A source domain represented by an abstract-basis
ideal completion. Reflexivity gives algebraicity of `Idl(B)` via Chapter 2, and
the order comparison records that `B` presents the source object. -/
structure IdealCompletionPresentation
    (D : OrderedDomain.{u}) (B : Chapter2.AbstractBasis.{u}) : Prop where
  reflexive : ∀ x : B.carrier, B.rel x x
  comparison :
    Nonempty (Chapter3.OrderIsoData (IdealCompletionDomain B).carrier D.carrier)

/-- The forward map of an order isomorphism is Scott-continuous. -/
theorem orderIsoData_toFun_scottContinuous
    {A : Type u} {B : Type v} [Preorder A] [Preorder B]
    (iso : Chapter3.OrderIsoData A B) :
    Chapter3.ScottContinuous iso.toFun := by
  constructor
  · exact iso.monotone_to
  · intro S s hS hs
    constructor
    · intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      exact iso.monotone_to (hs.1 ha)
    · intro y hy
      have hUpperInv : Chapter3.IsUpperBound S (iso.invFun y) := by
        intro a ha
        have hfa : iso.toFun a ≤ y := hy ⟨a, ha, rfl⟩
        calc
          a = iso.invFun (iso.toFun a) := (iso.left_inv a).symm
          _ ≤ iso.invFun y := iso.monotone_inv hfa
      have hsInv : s ≤ iso.invFun y := hs.2 (iso.invFun y) hUpperInv
      calc
        iso.toFun s ≤ iso.toFun (iso.invFun y) := iso.monotone_to hsInv
        _ = y := iso.right_inv y

/-- The inverse map of an order isomorphism is Scott-continuous. -/
theorem orderIsoData_invFun_scottContinuous
    {A : Type u} {B : Type v} [Preorder A] [Preorder B]
    (iso : Chapter3.OrderIsoData A B) :
    Chapter3.ScottContinuous iso.invFun := by
  constructor
  · exact iso.monotone_inv
  · intro S s hS hs
    constructor
    · intro y hy
      rcases hy with ⟨b, hb, rfl⟩
      exact iso.monotone_inv (hs.1 hb)
    · intro y hy
      have hUpperTo : Chapter3.IsUpperBound S (iso.toFun y) := by
        intro b hb
        have hby : iso.invFun b ≤ y := hy ⟨b, hb, rfl⟩
        calc
          b = iso.toFun (iso.invFun b) := (iso.right_inv b).symm
          _ ≤ iso.toFun y := iso.monotone_to hby
      have hsTo : s ≤ iso.toFun y := hs.2 (iso.toFun y) hUpperTo
      calc
        iso.invFun s ≤ iso.invFun (iso.toFun y) := iso.monotone_inv hsTo
        _ = y := iso.left_inv y

/-- An order isomorphism is a continuous section-retraction pair. -/
def orderIsoData_toContinuousSectionRetractionPair
    {A : Type u} {B : Type v} [Preorder A] [Preorder B]
    (iso : Chapter3.OrderIsoData A B) :
    Chapter3.ContinuousSectionRetractionPair A B where
  s := iso.toFun
  r := iso.invFun
  monotone_s := iso.monotone_to
  monotone_r := iso.monotone_inv
  retract := iso.left_inv
  continuous_s := orderIsoData_toFun_scottContinuous iso
  continuous_r := orderIsoData_invFun_scottContinuous iso

/-- Proposition 4.1.4 support: reflexive ideal completions are algebraic. -/
theorem idealCompletionDomain_algebraic_of_reflexive
    (B : Chapter2.AbstractBasis.{u}) (hreflexive : ∀ x : B.carrier, B.rel x x) :
    Chapter3.IsAlgebraicDomain (IdealCompletionDomain B).carrier := by
  change Chapter2.IsBasis (Chapter2.CompactSet : Set B.Ideal)
  exact Chapter2.prop_2_2_4_1
    (B.prop_2_2_22_4_reflexive_ideal_completion_algebraic hreflexive)

/-- Proposition 4.1.4, PDF text: "Let `D` be an L-domain
(bc-domain, continuous lattice). Then `Idl(D, ⊑)` is an algebraic L-domain
(bc-domain, lattice)."  The algebraicity is the reflexive ideal-completion
argument; the lattice-like structure transfers along the presentation
order-isomorphism. -/
theorem prop_4_1_4_ideal_completion_lattice_like
    (D : OrderedDomain.{u}) (B : Chapter2.AbstractBasis.{u})
    (hPresentation : IdealCompletionPresentation D B) :
    (IsLDomain D →
      Chapter3.IsAlgebraicDomain (IdealCompletionDomain B).carrier ∧
        IsLDomain (IdealCompletionDomain B)) ∧
      (IsBcDomain D →
        Chapter3.IsAlgebraicDomain (IdealCompletionDomain B).carrier ∧
          IsBcDomain (IdealCompletionDomain B)) ∧
        (IsContinuousLatticeDomain D →
          Chapter3.IsAlgebraicDomain (IdealCompletionDomain B).carrier ∧
            IsContinuousLatticeDomain (IdealCompletionDomain B)) := by
  rcases hPresentation.comparison with ⟨iso⟩
  let sr :
      Chapter3.ContinuousSectionRetractionPair
        (IdealCompletionDomain B).carrier D.carrier :=
    orderIsoData_toContinuousSectionRetractionPair iso
  have hTransfer :=
    prop_4_1_3_retracts_bilimits_lattice_like
      (D := IdealCompletionDomain B) (E := D) sr
  have hAlg : Chapter3.IsAlgebraicDomain (IdealCompletionDomain B).carrier :=
    idealCompletionDomain_algebraic_of_reflexive B hPresentation.reflexive
  constructor
  · intro hD
    exact ⟨hAlg, hTransfer.1 hD⟩
  constructor
  · intro hD
    exact ⟨hAlg, hTransfer.2.1 hD⟩
  · intro hD
    exact ⟨hAlg, hTransfer.2.2 hD⟩

/-- Constant continuous maps into an ordered domain. -/
def FunctionSpace.const
    (D E : OrderedDomain.{u}) (e : E.carrier) : OrderedDomain.ContFunCarrier D E where
  toFun := fun _ => e
  continuous := Chapter3.const_scottContinuous e

/-- Proposition 4.1.5 support: if the codomain has a bottom, the continuous
function space has the pointwise constant bottom. -/
theorem functionSpace_hasBottom_of_codomain
    (D E : OrderedDomain.{u}) (hbot : HasBottom E) :
    HasBottom (OrderedDomain.functionSpace D E) := by
  rcases hbot with ⟨botE, hbotE⟩
  refine ⟨FunctionSpace.const D E botE, ?_⟩
  intro f x
  exact hbotE (((f : OrderedDomain.ContFunCarrier D E).toFun) x)

/-- Proposition 4.1.5 support: the step-function approximation principle gives
the continuous-domain part of the function space, under the explicit dcpo
hypotheses implicit in the book's word "domain". -/
theorem functionSpace_continuousDomain_of_stepFunctionApproximation
    {D E : OrderedDomain.{u}} [OrderBot E.carrier]
    (hDdcpo : Chapter3.IsDcpo D.carrier) (hEdcpo : Chapter3.IsDcpo E.carrier)
    (hD : Chapter3.IsContinuousDomain D.carrier)
    (hE : Chapter3.IsContinuousDomain E.carrier)
    (hStep : StepFunctionApproximationData D.carrier E.carrier) :
    Chapter3.IsContinuousDomain (OrderedDomain.functionSpace D E).carrier := by
  classical
  refine ⟨Set.univ, ?_⟩
  apply Chapter2.prop_2_2_4_1
  intro f
  refine ⟨StepFunctionApproximationSet f, ?_, ?_, ?_⟩
  · intro g hg
    rcases hg with ⟨d, e, hApprox, rfl⟩
    exact ⟨trivial, hStep.step_approximates hDdcpo hEdcpo f d e hApprox⟩
  · exact hStep.step_approximants_directed hDdcpo hEdcpo hD hE f
  · exact hStep.continuous_sup_of_steps hDdcpo hEdcpo hD hE f

/-- Concrete data for proving that a function space is a continuous domain by
the step-function route of Proposition 4.0.2. The dcpo assumptions are explicit
because the local `IsContinuousDomain` predicate records a basis but does not
itself package directed suprema. -/
structure FunctionSpace.StepContinuityData
    (D E : OrderedDomain.{u}) where
  codomainOrderBot : OrderBot E.carrier
  domain_dcpo : Chapter3.IsDcpo D.carrier
  codomain_dcpo : Chapter3.IsDcpo E.carrier
  step :
    @StepFunctionApproximationData D.carrier E.carrier
      D.preorder E.preorder codomainOrderBot

/-- Step-continuity data gives the function-space continuous-domain component. -/
theorem FunctionSpace.continuousDomain_of_stepContinuityData
    {D E : OrderedDomain.{u}}
    (hD : Chapter3.IsContinuousDomain D.carrier)
    (hE : Chapter3.IsContinuousDomain E.carrier)
    (data : FunctionSpace.StepContinuityData D E) :
    Chapter3.IsContinuousDomain (OrderedDomain.functionSpace D E).carrier := by
  letI : OrderBot E.carrier := data.codomainOrderBot
  exact functionSpace_continuousDomain_of_stepFunctionApproximation
    data.domain_dcpo data.codomain_dcpo hD hE data.step

/-- Values at a fixed argument of a family of continuous functions. -/
def FunctionSpace.EvaluationSet
    (D E : OrderedDomain.{u}) (A : Set (OrderedDomain.ContFunCarrier D E))
    (x : D.carrier) : Set E.carrier :=
  {y : E.carrier | ∃ f ∈ A, y = ((f : OrderedDomain.ContFunCarrier D E).toFun) x}

/-- Pointwise infimum data for a family of continuous maps. The bundled `inf`
field records the Scott-continuity part; the `pointwise_inf` field records the
order-theoretic infimum at each input. -/
structure FunctionSpace.PointwiseInfimum
    (D E : OrderedDomain.{u}) (A : Set (OrderedDomain.ContFunCarrier D E)) where
  inf : OrderedDomain.ContFunCarrier D E
  pointwise_inf :
    ∀ x : D.carrier, Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) (inf x)

/-- The raw pointwise infimum function obtained by choosing coordinate infima. -/
noncomputable def FunctionSpace.pointwiseInfFun
    (D E : OrderedDomain.{u}) (A : Set (OrderedDomain.ContFunCarrier D E))
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i) :
    D.carrier → E.carrier :=
  fun x => Classical.choose (hcoord x)

/-- The chosen raw pointwise infimum is coordinatewise an infimum. -/
theorem FunctionSpace.pointwiseInfFun_isInf
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i) :
    ∀ x : D.carrier,
      Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x)
        (FunctionSpace.pointwiseInfFun D E A hcoord x) :=
  fun x => Classical.choose_spec (hcoord x)

/-- The chosen raw pointwise infimum is monotone. This proves the order-theoretic
half of its Scott-continuity; preservation of directed suprema is the remaining
nontrivial part. -/
theorem FunctionSpace.pointwiseInfFun_monotone
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i) :
    Monotone (FunctionSpace.pointwiseInfFun D E A hcoord) := by
  intro x y hxy
  have hxinf := FunctionSpace.pointwiseInfFun_isInf (D := D) (E := E) (A := A) hcoord x
  have hyinf := FunctionSpace.pointwiseInfFun_isInf (D := D) (E := E) (A := A) hcoord y
  exact hyinf.2 (FunctionSpace.pointwiseInfFun D E A hcoord x) (by
    intro z hz
    rcases hz with ⟨f, hf, rfl⟩
    exact le_trans (hxinf.1 ⟨f, hf, rfl⟩) (((f : OrderedDomain.ContFunCarrier D E).continuous).1 hxy))

/-- Concrete local case for Proposition 4.1.5: a family of continuous maps has a
least member in the pointwise order. In this case the chosen pointwise infimum is
equivalent to that member, so its continuity follows from the member's
continuity. -/
structure FunctionSpace.LeastMemberData
    (D E : OrderedDomain.{u}) (A : Set (OrderedDomain.ContFunCarrier D E)) where
  member : OrderedDomain.ContFunCarrier D E
  member_mem : member ∈ A
  member_le : ∀ g : OrderedDomain.ContFunCarrier D E, g ∈ A → member ≤ g

/-- A least member of a function family is its infimum in the pointwise
function-space order. -/
theorem FunctionSpace.leastMember_isInf
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    (data : FunctionSpace.LeastMemberData D E A) :
    Chapter3.IsInf A data.member := by
  constructor
  · intro f hf
    exact data.member_le f hf
  · intro g hg
    exact hg data.member_mem

/-- For a family with a least member, the least member is below the chosen
pointwise infimum at every input. -/
theorem FunctionSpace.leastMember_le_pointwiseInfFun
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (data : FunctionSpace.LeastMemberData D E A) (x : D.carrier) :
    data.member x ≤ FunctionSpace.pointwiseInfFun D E A hcoord x := by
  have hinf := FunctionSpace.pointwiseInfFun_isInf (D := D) (E := E) (A := A) hcoord x
  exact hinf.2 (data.member x) (by
    intro y hy
    rcases hy with ⟨g, hg, rfl⟩
    exact data.member_le g hg x)

/-- For a family with a least member, the chosen pointwise infimum is below that
least member at every input. -/
theorem FunctionSpace.pointwiseInfFun_le_leastMember
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (data : FunctionSpace.LeastMemberData D E A) (x : D.carrier) :
    FunctionSpace.pointwiseInfFun D E A hcoord x ≤ data.member x := by
  have hinf := FunctionSpace.pointwiseInfFun_isInf (D := D) (E := E) (A := A) hcoord x
  exact hinf.1 ⟨data.member, data.member_mem, rfl⟩

/-- Directed-supremum preservation for a chosen raw pointwise infimum function. -/
def FunctionSpace.PointwiseInfPreservesDirectedSups
    (D E : OrderedDomain.{u}) (A : Set (OrderedDomain.ContFunCarrier D E))
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i) : Prop :=
  ∀ ⦃S : Set D.carrier⦄ ⦃x : D.carrier⦄,
    Chapter3.DirectedSet S → Chapter3.IsSup S x →
      Chapter3.IsSup
        (FunctionSpace.pointwiseInfFun D E A hcoord '' S)
        (FunctionSpace.pointwiseInfFun D E A hcoord x)

/-- The least-upper-bound half of directed-supremum preservation for a chosen
raw pointwise infimum function. The upper-bound half follows from monotonicity. -/
def FunctionSpace.PointwiseInfDirectedSupLeast
    (D E : OrderedDomain.{u}) (A : Set (OrderedDomain.ContFunCarrier D E))
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i) : Prop :=
  ∀ ⦃S : Set D.carrier⦄ ⦃x : D.carrier⦄,
    Chapter3.DirectedSet S → Chapter3.IsSup S x →
      ∀ y : E.carrier,
        Chapter3.IsUpperBound (FunctionSpace.pointwiseInfFun D E A hcoord '' S) y →
          FunctionSpace.pointwiseInfFun D E A hcoord x ≤ y

/-- The chosen raw pointwise infimum is an upper bound of its image over a
directed supremum. This is the easy half of directed-supremum preservation. -/
theorem FunctionSpace.pointwiseInfFun_directedSup_upperBound
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i)
    {S : Set D.carrier} {x : D.carrier}
    (_hS : Chapter3.DirectedSet S) (hx : Chapter3.IsSup S x) :
    Chapter3.IsUpperBound
      (FunctionSpace.pointwiseInfFun D E A hcoord '' S)
      (FunctionSpace.pointwiseInfFun D E A hcoord x) := by
  intro y hy
  rcases hy with ⟨s, hs, rfl⟩
  exact FunctionSpace.pointwiseInfFun_monotone hcoord (hx.1 hs)

/-- Full directed-supremum preservation follows from the remaining
least-upper-bound half, since the upper-bound half is already proved. -/
theorem FunctionSpace.pointwiseInfPreservesDirectedSups_of_least
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (hleast : FunctionSpace.PointwiseInfDirectedSupLeast D E A hcoord) :
    FunctionSpace.PointwiseInfPreservesDirectedSups D E A hcoord := by
  intro S x hS hx
  exact ⟨
    FunctionSpace.pointwiseInfFun_directedSup_upperBound hcoord hS hx,
    hleast hS hx⟩

/-- Full directed-supremum preservation immediately supplies the remaining
least-upper-bound half. -/
theorem FunctionSpace.pointwiseInfDirectedSupLeast_of_preservesDirectedSups
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (hpres : FunctionSpace.PointwiseInfPreservesDirectedSups D E A hcoord) :
    FunctionSpace.PointwiseInfDirectedSupLeast D E A hcoord := by
  intro S x hS hx y hy
  exact (hpres hS hx).2 y hy

/-- Since the upper-bound half follows from monotonicity, the remaining
least-upper-bound half is equivalent to full directed-supremum preservation. -/
theorem FunctionSpace.pointwiseInfPreservesDirectedSups_iff_least
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i} :
    FunctionSpace.PointwiseInfPreservesDirectedSups D E A hcoord ↔
      FunctionSpace.PointwiseInfDirectedSupLeast D E A hcoord := by
  constructor
  · exact FunctionSpace.pointwiseInfDirectedSupLeast_of_preservesDirectedSups
  · exact FunctionSpace.pointwiseInfPreservesDirectedSups_of_least

/-- Local infimum/supremum exchange law for Proposition 4.1.5: at a directed
supremum `x`, the chosen pointwise infimum is below the supremum of the chosen
pointwise infima over the directed set. This is the mathematical content hidden
inside the remaining least-upper-bound half. -/
def FunctionSpace.PointwiseInfDirectedSupExchange
    (D E : OrderedDomain.{u}) (A : Set (OrderedDomain.ContFunCarrier D E))
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i) : Prop :=
  ∀ ⦃S : Set D.carrier⦄ ⦃x : D.carrier⦄,
    Chapter3.DirectedSet S → Chapter3.IsSup S x →
      ∃ s : E.carrier,
        Chapter3.IsSup (FunctionSpace.pointwiseInfFun D E A hcoord '' S) s ∧
          FunctionSpace.pointwiseInfFun D E A hcoord x ≤ s

/-- The local infimum/supremum exchange law implies the remaining
least-upper-bound half of directed-supremum preservation. -/
theorem FunctionSpace.pointwiseInfDirectedSupLeast_of_directedSupExchange
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (hexchange : FunctionSpace.PointwiseInfDirectedSupExchange D E A hcoord) :
    FunctionSpace.PointwiseInfDirectedSupLeast D E A hcoord := by
  intro S x hS hx y hy
  rcases hexchange hS hx with ⟨s, hs, hxs⟩
  exact le_trans hxs (hs.2 y hy)

/-- The remaining least-upper-bound half supplies the local infimum/supremum
exchange law, since the chosen pointwise infimum at the directed supremum is
then itself the supremum of the image. -/
theorem FunctionSpace.pointwiseInfDirectedSupExchange_of_least
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (hleast : FunctionSpace.PointwiseInfDirectedSupLeast D E A hcoord) :
    FunctionSpace.PointwiseInfDirectedSupExchange D E A hcoord := by
  intro S x hS hx
  exact ⟨FunctionSpace.pointwiseInfFun D E A hcoord x,
    FunctionSpace.pointwiseInfPreservesDirectedSups_of_least hleast hS hx,
    le_rfl⟩

/-- The exchange-law formulation is equivalent to the current least-half
formulation. This gives a more semantic target for future Proposition 4.1.5 proof
work. -/
theorem FunctionSpace.pointwiseInfDirectedSupExchange_iff_least
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i} :
    FunctionSpace.PointwiseInfDirectedSupExchange D E A hcoord ↔
      FunctionSpace.PointwiseInfDirectedSupLeast D E A hcoord := by
  constructor
  · exact FunctionSpace.pointwiseInfDirectedSupLeast_of_directedSupExchange
  · exact FunctionSpace.pointwiseInfDirectedSupExchange_of_least

/-- Full directed-supremum preservation also supplies the exchange-law
formulation. -/
theorem FunctionSpace.pointwiseInfDirectedSupExchange_of_preservesDirectedSups
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (hpres : FunctionSpace.PointwiseInfPreservesDirectedSups D E A hcoord) :
    FunctionSpace.PointwiseInfDirectedSupExchange D E A hcoord :=
  FunctionSpace.pointwiseInfDirectedSupExchange_of_least
    (FunctionSpace.pointwiseInfDirectedSupLeast_of_preservesDirectedSups hpres)

/-- If the family has a least continuous member, the chosen pointwise infimum
satisfies the remaining directed-supremum least-upper-bound half. -/
theorem FunctionSpace.pointwiseInfDirectedSupLeast_of_leastMember
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (data : FunctionSpace.LeastMemberData D E A) :
    FunctionSpace.PointwiseInfDirectedSupLeast D E A hcoord := by
  intro S x hS hx y hy
  have hMemberSup :
      Chapter3.IsSup ((fun s : D.carrier => data.member s) '' S) (data.member x) :=
    data.member.continuous.2 hS hx
  have hyMemberUpper :
      Chapter3.IsUpperBound ((fun s : D.carrier => data.member s) '' S) y := by
    intro z hz
    rcases hz with ⟨s, hs, rfl⟩
    exact le_trans
      (FunctionSpace.leastMember_le_pointwiseInfFun (D := D) (E := E) (A := A)
        (hcoord := hcoord) data s)
      (hy ⟨s, hs, rfl⟩)
  exact le_trans
    (FunctionSpace.pointwiseInfFun_le_leastMember (D := D) (E := E) (A := A)
      (hcoord := hcoord) data x)
    (hMemberSup.2 y hyMemberUpper)

/-- If the family has a least continuous member, the chosen pointwise infimum
preserves directed suprema. -/
theorem FunctionSpace.pointwiseInfPreservesDirectedSups_of_leastMember
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (data : FunctionSpace.LeastMemberData D E A) :
    FunctionSpace.PointwiseInfPreservesDirectedSups D E A hcoord :=
  FunctionSpace.pointwiseInfPreservesDirectedSups_of_least
    (FunctionSpace.pointwiseInfDirectedSupLeast_of_leastMember data)

/-- The least-member local case also supplies the exchange-law formulation. -/
theorem FunctionSpace.pointwiseInfDirectedSupExchange_of_leastMember
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (data : FunctionSpace.LeastMemberData D E A) :
    FunctionSpace.PointwiseInfDirectedSupExchange D E A hcoord :=
  FunctionSpace.pointwiseInfDirectedSupExchange_of_least
    (FunctionSpace.pointwiseInfDirectedSupLeast_of_leastMember data)

/-- If the chosen raw pointwise infimum preserves all existing suprema, then it
satisfies the remaining directed-supremum least-upper-bound half. -/
theorem FunctionSpace.pointwiseInfDirectedSupLeast_of_preservesAllSuprema
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i)
    (hpres :
      Chapter3.PreservesAllSuprema (FunctionSpace.pointwiseInfFun D E A hcoord)) :
    FunctionSpace.PointwiseInfDirectedSupLeast D E A hcoord := by
  intro S x _hS hx y hy
  exact (hpres S x hx).2 y hy

/-- Preservation of all existing suprema supplies the exchange-law formulation. -/
theorem FunctionSpace.pointwiseInfDirectedSupExchange_of_preservesAllSuprema
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i)
    (hpres :
      Chapter3.PreservesAllSuprema (FunctionSpace.pointwiseInfFun D E A hcoord)) :
    FunctionSpace.PointwiseInfDirectedSupExchange D E A hcoord :=
  FunctionSpace.pointwiseInfDirectedSupExchange_of_least
    (FunctionSpace.pointwiseInfDirectedSupLeast_of_preservesAllSuprema hcoord hpres)

/-- A lower-adjoint presentation of the chosen raw pointwise infimum is a
standard sufficient condition for the remaining directed-supremum least half. -/
theorem FunctionSpace.pointwiseInfDirectedSupLeast_of_lowerAdjoint
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i)
    {g : E.carrier → D.carrier}
    (hadj : Chapter3.Adjunction (FunctionSpace.pointwiseInfFun D E A hcoord) g) :
    FunctionSpace.PointwiseInfDirectedSupLeast D E A hcoord :=
  FunctionSpace.pointwiseInfDirectedSupLeast_of_preservesAllSuprema hcoord
    (fun _ _ hx => Chapter3.lower_adjoint_preserves_sup hadj hx)

/-- A lower-adjoint presentation also supplies the exchange-law formulation. -/
theorem FunctionSpace.pointwiseInfDirectedSupExchange_of_lowerAdjoint
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i)
    {g : E.carrier → D.carrier}
    (hadj : Chapter3.Adjunction (FunctionSpace.pointwiseInfFun D E A hcoord) g) :
    FunctionSpace.PointwiseInfDirectedSupExchange D E A hcoord :=
  FunctionSpace.pointwiseInfDirectedSupExchange_of_least
    (FunctionSpace.pointwiseInfDirectedSupLeast_of_lowerAdjoint hcoord hadj)

/-- A `HasUpperAdjoint` witness for the chosen raw pointwise infimum is the
same standard sufficient condition, using Chapter 3's naming convention for a
map that has an upper adjoint. -/
theorem FunctionSpace.pointwiseInfDirectedSupLeast_of_hasUpperAdjoint
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i)
    (hadj : Chapter3.HasUpperAdjoint (FunctionSpace.pointwiseInfFun D E A hcoord)) :
    FunctionSpace.PointwiseInfDirectedSupLeast D E A hcoord := by
  rcases hadj with ⟨g, hg⟩
  exact FunctionSpace.pointwiseInfDirectedSupLeast_of_lowerAdjoint hcoord hg

/-- A `HasUpperAdjoint` witness also supplies the exchange-law formulation. -/
theorem FunctionSpace.pointwiseInfDirectedSupExchange_of_hasUpperAdjoint
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i)
    (hadj : Chapter3.HasUpperAdjoint (FunctionSpace.pointwiseInfFun D E A hcoord)) :
    FunctionSpace.PointwiseInfDirectedSupExchange D E A hcoord :=
  FunctionSpace.pointwiseInfDirectedSupExchange_of_least
    (FunctionSpace.pointwiseInfDirectedSupLeast_of_hasUpperAdjoint hcoord hadj)

/-- A `HasUpperAdjoint` witness for the chosen raw pointwise infimum directly
gives Scott-continuity, since it makes the raw pointwise infimum a lower
adjoint. -/
theorem FunctionSpace.pointwiseInfFun_scottContinuous_of_hasUpperAdjoint
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i)
    (hadj : Chapter3.HasUpperAdjoint (FunctionSpace.pointwiseInfFun D E A hcoord)) :
    Chapter3.ScottContinuous (FunctionSpace.pointwiseInfFun D E A hcoord) := by
  rcases hadj with ⟨g, hg⟩
  exact Chapter3.lower_adjoint_scottContinuous hg

/-- Concrete upper-adjoint data for a chosen raw pointwise-infimum map. This is
the data-level form of `HasUpperAdjoint`: the proposed upper map is exposed as a
field, which is useful when later replacing registered proof debt by actual
constructions. -/
structure FunctionSpace.PointwiseInfUpperAdjointData
    (D E : OrderedDomain.{u}) (A : Set (OrderedDomain.ContFunCarrier D E))
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i) where
  upper : E.carrier → D.carrier
  adjunction : Chapter3.Adjunction (FunctionSpace.pointwiseInfFun D E A hcoord) upper

/-- Concrete upper-adjoint data packages a `HasUpperAdjoint` witness. -/
theorem FunctionSpace.pointwiseInfHasUpperAdjoint_of_upperAdjointData
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (data : FunctionSpace.PointwiseInfUpperAdjointData D E A hcoord) :
    Chapter3.HasUpperAdjoint (FunctionSpace.pointwiseInfFun D E A hcoord) :=
  ⟨data.upper, data.adjunction⟩

/-- Concrete upper-adjoint data is a sufficient condition for the remaining
directed-supremum least-upper-bound half. -/
theorem FunctionSpace.pointwiseInfDirectedSupLeast_of_upperAdjointData
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (data : FunctionSpace.PointwiseInfUpperAdjointData D E A hcoord) :
    FunctionSpace.PointwiseInfDirectedSupLeast D E A hcoord :=
  FunctionSpace.pointwiseInfDirectedSupLeast_of_hasUpperAdjoint hcoord
    (FunctionSpace.pointwiseInfHasUpperAdjoint_of_upperAdjointData data)

/-- Concrete upper-adjoint data also supplies the exchange-law formulation. -/
theorem FunctionSpace.pointwiseInfDirectedSupExchange_of_upperAdjointData
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (data : FunctionSpace.PointwiseInfUpperAdjointData D E A hcoord) :
    FunctionSpace.PointwiseInfDirectedSupExchange D E A hcoord :=
  FunctionSpace.pointwiseInfDirectedSupExchange_of_least
    (FunctionSpace.pointwiseInfDirectedSupLeast_of_upperAdjointData data)

/-- Concrete upper-adjoint data also gives Scott-continuity of the chosen raw
pointwise infimum directly. -/
theorem FunctionSpace.pointwiseInfFun_scottContinuous_of_upperAdjointData
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (data : FunctionSpace.PointwiseInfUpperAdjointData D E A hcoord) :
    Chapter3.ScottContinuous (FunctionSpace.pointwiseInfFun D E A hcoord) :=
  FunctionSpace.pointwiseInfFun_scottContinuous_of_hasUpperAdjoint hcoord
    (FunctionSpace.pointwiseInfHasUpperAdjoint_of_upperAdjointData data)

/-- A chosen raw pointwise infimum is Scott-continuous once directed-supremum
preservation is supplied. -/
theorem FunctionSpace.pointwiseInfFun_scottContinuous_of_preservesDirectedSups
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i)
    (hpres : FunctionSpace.PointwiseInfPreservesDirectedSups D E A hcoord) :
    Chapter3.ScottContinuous (FunctionSpace.pointwiseInfFun D E A hcoord) := by
  exact ⟨FunctionSpace.pointwiseInfFun_monotone hcoord, hpres⟩

/-- Scott-continuity of the chosen raw pointwise infimum includes preservation
of directed suprema. -/
theorem FunctionSpace.pointwiseInfPreservesDirectedSups_of_scottContinuous
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (hcontinuous :
      Chapter3.ScottContinuous (FunctionSpace.pointwiseInfFun D E A hcoord)) :
    FunctionSpace.PointwiseInfPreservesDirectedSups D E A hcoord := by
  intro S x hS hx
  exact hcontinuous.2 hS hx

/-- Scott-continuity of the chosen raw pointwise infimum is therefore enough for
the remaining least-upper-bound half. -/
theorem FunctionSpace.pointwiseInfDirectedSupLeast_of_scottContinuous
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (hcontinuous :
      Chapter3.ScottContinuous (FunctionSpace.pointwiseInfFun D E A hcoord)) :
    FunctionSpace.PointwiseInfDirectedSupLeast D E A hcoord :=
  FunctionSpace.pointwiseInfDirectedSupLeast_of_preservesDirectedSups
    (FunctionSpace.pointwiseInfPreservesDirectedSups_of_scottContinuous hcontinuous)

/-- Scott-continuity of the chosen raw pointwise infimum also supplies the
exchange-law formulation. -/
theorem FunctionSpace.pointwiseInfDirectedSupExchange_of_scottContinuous
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (hcontinuous :
      Chapter3.ScottContinuous (FunctionSpace.pointwiseInfFun D E A hcoord)) :
    FunctionSpace.PointwiseInfDirectedSupExchange D E A hcoord :=
  FunctionSpace.pointwiseInfDirectedSupExchange_of_least
    (FunctionSpace.pointwiseInfDirectedSupLeast_of_scottContinuous hcontinuous)

/-- If the family has a least continuous member, the chosen pointwise infimum is
Scott-continuous. -/
theorem FunctionSpace.pointwiseInfFun_scottContinuous_of_leastMember
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i)
    (data : FunctionSpace.LeastMemberData D E A) :
    Chapter3.ScottContinuous (FunctionSpace.pointwiseInfFun D E A hcoord) :=
  FunctionSpace.pointwiseInfFun_scottContinuous_of_preservesDirectedSups hcoord
    (FunctionSpace.pointwiseInfPreservesDirectedSups_of_leastMember data)

/-- A Scott-continuous raw pointwise infimum gives bundled pointwise-infimum data. -/
noncomputable def FunctionSpace.pointwiseInfimum_of_continuous_choice
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    (hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i)
    (hcontinuous : Chapter3.ScottContinuous (FunctionSpace.pointwiseInfFun D E A hcoord)) :
    FunctionSpace.PointwiseInfimum D E A where
  inf := {
    toFun := FunctionSpace.pointwiseInfFun D E A hcoord
    continuous := hcontinuous
  }
  pointwise_inf := FunctionSpace.pointwiseInfFun_isInf hcoord

/-- Concrete upper-adjoint data gives bundled pointwise-infimum data without
separately passing through the directed-supremum least-half formulation. -/
noncomputable def FunctionSpace.pointwiseInfimum_of_upperAdjointData
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (data : FunctionSpace.PointwiseInfUpperAdjointData D E A hcoord) :
    FunctionSpace.PointwiseInfimum D E A :=
  FunctionSpace.pointwiseInfimum_of_continuous_choice hcoord
    (FunctionSpace.pointwiseInfFun_scottContinuous_of_upperAdjointData data)

/-- If the family has a least continuous member, the chosen pointwise infimum
bundles to an infimum in the function space. -/
noncomputable def FunctionSpace.pointwiseInfimum_of_leastMember
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {hcoord :
      ∀ x : D.carrier, ∃ i : E.carrier,
        Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i}
    (data : FunctionSpace.LeastMemberData D E A) :
    FunctionSpace.PointwiseInfimum D E A :=
  FunctionSpace.pointwiseInfimum_of_continuous_choice hcoord
    (FunctionSpace.pointwiseInfFun_scottContinuous_of_leastMember hcoord data)

/-- Pointwise infimum data gives an infimum in the function-space order. -/
theorem FunctionSpace.pointwiseInfimum_isInf
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    (data : FunctionSpace.PointwiseInfimum D E A) :
    Chapter3.IsInf A data.inf := by
  constructor
  · intro f hf x
    exact (data.pointwise_inf x).1 ⟨f, hf, rfl⟩
  · intro g hg x
    exact (data.pointwise_inf x).2 (((g : OrderedDomain.ContFunCarrier D E).toFun) x) (by
      intro y hy
      rcases hy with ⟨f, hf, rfl⟩
      exact hg hf x)

/-- All function-space infima follow from pointwise-infimum data for every
family of continuous maps. -/
theorem functionSpace_hasAllInfima_of_pointwiseInfimum
    {D E : OrderedDomain.{u}}
    (hPointwise :
      ∀ A : Set (OrderedDomain.ContFunCarrier D E),
        Nonempty (FunctionSpace.PointwiseInfimum D E A)) :
    HasAllInfima (OrderedDomain.functionSpace D E) := by
  intro A
  rcases hPointwise A with ⟨data⟩
  exact ⟨data.inf, FunctionSpace.pointwiseInfimum_isInf data⟩

/-- Nonempty function-space infima follow from pointwise-infimum data for every
nonempty family of continuous maps. -/
theorem functionSpace_hasNonemptyInfima_of_pointwiseInfimum
    {D E : OrderedDomain.{u}}
    (hPointwise :
      ∀ A : Set (OrderedDomain.ContFunCarrier D E), A.Nonempty →
        Nonempty (FunctionSpace.PointwiseInfimum D E A)) :
    HasNonemptyInfima (OrderedDomain.functionSpace D E) := by
  intro A hA
  rcases hPointwise A hA with ⟨data⟩
  exact ⟨data.inf, FunctionSpace.pointwiseInfimum_isInf data⟩

/-- Principal-lower function-space infima follow from pointwise-infimum data for
every nonempty family contained in a principal lower set. -/
theorem functionSpace_hasPrincipalLowerInfima_of_pointwiseInfimum
    {D E : OrderedDomain.{u}}
    (hPointwise :
      ∀ f : OrderedDomain.ContFunCarrier D E,
        ∀ A : Set (OrderedDomain.ContFunCarrier D E),
          A.Nonempty → A ⊆ {g : OrderedDomain.ContFunCarrier D E | g ≤ f} →
            Nonempty (FunctionSpace.PointwiseInfimum D E A)) :
    HasPrincipalLowerInfima (OrderedDomain.functionSpace D E) := by
  intro f A hA hAf
  rcases hPointwise f A hA hAf with ⟨data⟩
  exact ⟨data.inf, FunctionSpace.pointwiseInfimum_isInf data⟩

/-- Evaluation of a nonempty family of functions is nonempty at every argument. -/
theorem FunctionSpace.evaluationSet_nonempty
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    (hA : A.Nonempty) (x : D.carrier) :
    (FunctionSpace.EvaluationSet D E A x).Nonempty := by
  rcases hA with ⟨f, hf⟩
  exact ⟨f x, f, hf, rfl⟩

/-- If a family of functions lies below `f`, then every evaluation set lies
below the corresponding value of `f`. -/
theorem FunctionSpace.evaluationSet_subset_principal
    {D E : OrderedDomain.{u}} {A : Set (OrderedDomain.ContFunCarrier D E)}
    {f : OrderedDomain.ContFunCarrier D E}
    (hAf : A ⊆ {g : OrderedDomain.ContFunCarrier D E | g ≤ f}) (x : D.carrier) :
    FunctionSpace.EvaluationSet D E A x ⊆ {y : E.carrier | y ≤ f x} := by
  intro y hy
  rcases hy with ⟨g, hg, rfl⟩
  exact hAf hg x

/-- Coordinate infima supplied by arbitrary infima in the codomain. -/
noncomputable def FunctionSpace.allPointwiseInfCoord
    {D E : OrderedDomain.{u}} (hinf : HasAllInfima E)
    (A : Set (OrderedDomain.ContFunCarrier D E)) :
    ∀ x : D.carrier, ∃ i : E.carrier,
      Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i :=
  fun x => hinf (FunctionSpace.EvaluationSet D E A x)

/-- Coordinate infima supplied by nonempty infima in the codomain. -/
noncomputable def FunctionSpace.nonemptyPointwiseInfCoord
    {D E : OrderedDomain.{u}} (hinf : HasNonemptyInfima E)
    (A : Set (OrderedDomain.ContFunCarrier D E)) (hA : A.Nonempty) :
    ∀ x : D.carrier, ∃ i : E.carrier,
      Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i :=
  fun x => hinf (FunctionSpace.EvaluationSet D E A x)
    (FunctionSpace.evaluationSet_nonempty hA x)

/-- Coordinate infima supplied by principal-lower infima in the codomain. -/
noncomputable def FunctionSpace.principalLowerPointwiseInfCoord
    {D E : OrderedDomain.{u}} (hinf : HasPrincipalLowerInfima E)
    (f : OrderedDomain.ContFunCarrier D E)
    (A : Set (OrderedDomain.ContFunCarrier D E)) (hA : A.Nonempty)
    (hAf : A ⊆ {g : OrderedDomain.ContFunCarrier D E | g ≤ f}) :
    ∀ x : D.carrier, ∃ i : E.carrier,
      Chapter3.IsInf (FunctionSpace.EvaluationSet D E A x) i :=
  fun x => hinf (f x) (FunctionSpace.EvaluationSet D E A x)
    (FunctionSpace.evaluationSet_nonempty hA x)
    (FunctionSpace.evaluationSet_subset_principal hAf x)

/-- Principal-lower function-space infima follow directly when every such
family has a least member in the pointwise order. -/
theorem functionSpace_hasPrincipalLowerInfima_of_leastMembers
    {D E : OrderedDomain.{u}}
    (hLeast :
      ∀ f : OrderedDomain.ContFunCarrier D E,
        ∀ A : Set (OrderedDomain.ContFunCarrier D E),
          A.Nonempty → A ⊆ {g : OrderedDomain.ContFunCarrier D E | g ≤ f} →
            FunctionSpace.LeastMemberData D E A) :
    HasPrincipalLowerInfima (OrderedDomain.functionSpace D E) := by
  intro f A hA hAf
  exact ⟨(hLeast f A hA hAf).member,
    FunctionSpace.leastMember_isInf (hLeast f A hA hAf)⟩

/-- Nonempty function-space infima follow directly when every nonempty family
has a least member in the pointwise order. -/
theorem functionSpace_hasNonemptyInfima_of_leastMembers
    {D E : OrderedDomain.{u}}
    (hLeast :
      ∀ A : Set (OrderedDomain.ContFunCarrier D E), A.Nonempty →
        FunctionSpace.LeastMemberData D E A) :
    HasNonemptyInfima (OrderedDomain.functionSpace D E) := by
  intro A hA
  exact ⟨(hLeast A hA).member, FunctionSpace.leastMember_isInf (hLeast A hA)⟩

/-- Arbitrary function-space infima follow from nonempty least-member data plus
the codomain's empty infimum, which gives the pointwise top function. -/
theorem functionSpace_hasAllInfima_of_nonemptyLeastMembers
    {D E : OrderedDomain.{u}} (hinf : HasAllInfima E)
    (hLeast :
      ∀ A : Set (OrderedDomain.ContFunCarrier D E), A.Nonempty →
        FunctionSpace.LeastMemberData D E A) :
    HasAllInfima (OrderedDomain.functionSpace D E) := by
  intro A
  by_cases hA : A.Nonempty
  · exact ⟨(hLeast A hA).member, FunctionSpace.leastMember_isInf (hLeast A hA)⟩
  · rcases hinf (∅ : Set E.carrier) with ⟨topE, htopE⟩
    refine ⟨FunctionSpace.const D E topE, ?_⟩
    constructor
    · intro f hf
      exact False.elim (hA ⟨f, hf⟩)
    · intro g _hg x
      exact htopE.2 (((g : OrderedDomain.ContFunCarrier D E).toFun) x) (by
        intro y hy
        exact False.elim hy)

/-- Arbitrary function-space infima follow directly from concrete
upper-adjoint data for the chosen pointwise infimum functions. -/
theorem functionSpace_hasAllInfima_of_pointwiseInfUpperAdjointData
    {D E : OrderedDomain.{u}} (hinf : HasAllInfima E)
    (hadjData :
      ∀ A : Set (OrderedDomain.ContFunCarrier D E),
        FunctionSpace.PointwiseInfUpperAdjointData D E A
          (FunctionSpace.allPointwiseInfCoord hinf A)) :
    HasAllInfima (OrderedDomain.functionSpace D E) := by
  exact functionSpace_hasAllInfima_of_pointwiseInfimum (fun A =>
    ⟨FunctionSpace.pointwiseInfimum_of_upperAdjointData (hadjData A)⟩)

/-- Nonempty function-space infima follow directly from concrete
upper-adjoint data for the chosen pointwise infimum functions. -/
theorem functionSpace_hasNonemptyInfima_of_pointwiseInfUpperAdjointData
    {D E : OrderedDomain.{u}} (hinf : HasNonemptyInfima E)
    (hadjData :
      ∀ A : Set (OrderedDomain.ContFunCarrier D E), ∀ hA : A.Nonempty,
        FunctionSpace.PointwiseInfUpperAdjointData D E A
          (FunctionSpace.nonemptyPointwiseInfCoord hinf A hA)) :
    HasNonemptyInfima (OrderedDomain.functionSpace D E) := by
  exact functionSpace_hasNonemptyInfima_of_pointwiseInfimum (fun A hA =>
    ⟨FunctionSpace.pointwiseInfimum_of_upperAdjointData (hadjData A hA)⟩)

/-- Principal-lower function-space infima follow directly from concrete
upper-adjoint data for the chosen pointwise infimum functions. -/
theorem functionSpace_hasPrincipalLowerInfima_of_pointwiseInfUpperAdjointData
    {D E : OrderedDomain.{u}} (hinf : HasPrincipalLowerInfima E)
    (hadjData :
      ∀ f : OrderedDomain.ContFunCarrier D E,
        ∀ A : Set (OrderedDomain.ContFunCarrier D E),
          ∀ hA : A.Nonempty,
            ∀ hAf : A ⊆ {g : OrderedDomain.ContFunCarrier D E | g ≤ f},
              FunctionSpace.PointwiseInfUpperAdjointData D E A
                (FunctionSpace.principalLowerPointwiseInfCoord hinf f A hA hAf)) :
    HasPrincipalLowerInfima (OrderedDomain.functionSpace D E) := by
  exact functionSpace_hasPrincipalLowerInfima_of_pointwiseInfimum (fun f A hA hAf =>
    ⟨FunctionSpace.pointwiseInfimum_of_upperAdjointData (hadjData f A hA hAf)⟩)

/-- Arbitrary function-space infima follow once the chosen pointwise infimum
functions are Scott-continuous. -/
theorem functionSpace_hasAllInfima_of_pointwiseInfContinuity
    {D E : OrderedDomain.{u}} (hinf : HasAllInfima E)
    (hcontinuous :
      ∀ A : Set (OrderedDomain.ContFunCarrier D E),
        Chapter3.ScottContinuous
          (FunctionSpace.pointwiseInfFun D E A
            (FunctionSpace.allPointwiseInfCoord hinf A))) :
    HasAllInfima (OrderedDomain.functionSpace D E) := by
  exact functionSpace_hasAllInfima_of_pointwiseInfimum (fun A =>
    ⟨FunctionSpace.pointwiseInfimum_of_continuous_choice
      (FunctionSpace.allPointwiseInfCoord hinf A) (hcontinuous A)⟩)

/-- Nonempty function-space infima follow once the chosen pointwise infimum
functions are Scott-continuous. -/
theorem functionSpace_hasNonemptyInfima_of_pointwiseInfContinuity
    {D E : OrderedDomain.{u}} (hinf : HasNonemptyInfima E)
    (hcontinuous :
      ∀ A : Set (OrderedDomain.ContFunCarrier D E), ∀ hA : A.Nonempty,
        Chapter3.ScottContinuous
          (FunctionSpace.pointwiseInfFun D E A
            (FunctionSpace.nonemptyPointwiseInfCoord hinf A hA))) :
    HasNonemptyInfima (OrderedDomain.functionSpace D E) := by
  exact functionSpace_hasNonemptyInfima_of_pointwiseInfimum (fun A hA =>
    ⟨FunctionSpace.pointwiseInfimum_of_continuous_choice
      (FunctionSpace.nonemptyPointwiseInfCoord hinf A hA) (hcontinuous A hA)⟩)

/-- Principal-lower function-space infima follow once the chosen pointwise
infimum functions are Scott-continuous. -/
theorem functionSpace_hasPrincipalLowerInfima_of_pointwiseInfContinuity
    {D E : OrderedDomain.{u}} (hinf : HasPrincipalLowerInfima E)
    (hcontinuous :
      ∀ f : OrderedDomain.ContFunCarrier D E,
        ∀ A : Set (OrderedDomain.ContFunCarrier D E),
          ∀ hA : A.Nonempty,
            ∀ hAf : A ⊆ {g : OrderedDomain.ContFunCarrier D E | g ≤ f},
              Chapter3.ScottContinuous
                (FunctionSpace.pointwiseInfFun D E A
                  (FunctionSpace.principalLowerPointwiseInfCoord hinf f A hA hAf))) :
    HasPrincipalLowerInfima (OrderedDomain.functionSpace D E) := by
  exact functionSpace_hasPrincipalLowerInfima_of_pointwiseInfimum (fun f A hA hAf =>
    ⟨FunctionSpace.pointwiseInfimum_of_continuous_choice
      (FunctionSpace.principalLowerPointwiseInfCoord hinf f A hA hAf)
      (hcontinuous f A hA hAf)⟩)

/-- Arbitrary function-space infima follow once the chosen pointwise infimum
functions preserve directed suprema. Monotonicity is proved by
`FunctionSpace.pointwiseInfFun_monotone`. -/
theorem functionSpace_hasAllInfima_of_pointwiseInfDirectedSup
    {D E : OrderedDomain.{u}} (hinf : HasAllInfima E)
    (hpres :
      ∀ A : Set (OrderedDomain.ContFunCarrier D E),
        FunctionSpace.PointwiseInfPreservesDirectedSups D E A
          (FunctionSpace.allPointwiseInfCoord hinf A)) :
    HasAllInfima (OrderedDomain.functionSpace D E) := by
  exact functionSpace_hasAllInfima_of_pointwiseInfContinuity hinf (fun A =>
    FunctionSpace.pointwiseInfFun_scottContinuous_of_preservesDirectedSups
      (FunctionSpace.allPointwiseInfCoord hinf A) (hpres A))

/-- Nonempty function-space infima follow once the chosen pointwise infimum
functions preserve directed suprema. -/
theorem functionSpace_hasNonemptyInfima_of_pointwiseInfDirectedSup
    {D E : OrderedDomain.{u}} (hinf : HasNonemptyInfima E)
    (hpres :
      ∀ A : Set (OrderedDomain.ContFunCarrier D E), ∀ hA : A.Nonempty,
        FunctionSpace.PointwiseInfPreservesDirectedSups D E A
          (FunctionSpace.nonemptyPointwiseInfCoord hinf A hA)) :
    HasNonemptyInfima (OrderedDomain.functionSpace D E) := by
  exact functionSpace_hasNonemptyInfima_of_pointwiseInfContinuity hinf (fun A hA =>
    FunctionSpace.pointwiseInfFun_scottContinuous_of_preservesDirectedSups
      (FunctionSpace.nonemptyPointwiseInfCoord hinf A hA) (hpres A hA))

/-- Principal-lower function-space infima follow once the chosen pointwise
infimum functions preserve directed suprema. -/
theorem functionSpace_hasPrincipalLowerInfima_of_pointwiseInfDirectedSup
    {D E : OrderedDomain.{u}} (hinf : HasPrincipalLowerInfima E)
    (hpres :
      ∀ f : OrderedDomain.ContFunCarrier D E,
        ∀ A : Set (OrderedDomain.ContFunCarrier D E),
          ∀ hA : A.Nonempty,
            ∀ hAf : A ⊆ {g : OrderedDomain.ContFunCarrier D E | g ≤ f},
              FunctionSpace.PointwiseInfPreservesDirectedSups D E A
                (FunctionSpace.principalLowerPointwiseInfCoord hinf f A hA hAf)) :
    HasPrincipalLowerInfima (OrderedDomain.functionSpace D E) := by
  exact functionSpace_hasPrincipalLowerInfima_of_pointwiseInfContinuity hinf (fun f A hA hAf =>
    FunctionSpace.pointwiseInfFun_scottContinuous_of_preservesDirectedSups
      (FunctionSpace.principalLowerPointwiseInfCoord hinf f A hA hAf)
      (hpres f A hA hAf))

/-- Arbitrary function-space infima follow once the chosen pointwise infimum
functions satisfy the remaining directed-supremum least-upper-bound half. -/
theorem functionSpace_hasAllInfima_of_pointwiseInfDirectedSupLeast
    {D E : OrderedDomain.{u}} (hinf : HasAllInfima E)
    (hleast :
      ∀ A : Set (OrderedDomain.ContFunCarrier D E),
        FunctionSpace.PointwiseInfDirectedSupLeast D E A
          (FunctionSpace.allPointwiseInfCoord hinf A)) :
    HasAllInfima (OrderedDomain.functionSpace D E) := by
  exact functionSpace_hasAllInfima_of_pointwiseInfDirectedSup hinf (fun A =>
    FunctionSpace.pointwiseInfPreservesDirectedSups_of_least (hleast A))

/-- Nonempty function-space infima follow once the chosen pointwise infimum
functions satisfy the remaining directed-supremum least-upper-bound half. -/
theorem functionSpace_hasNonemptyInfima_of_pointwiseInfDirectedSupLeast
    {D E : OrderedDomain.{u}} (hinf : HasNonemptyInfima E)
    (hleast :
      ∀ A : Set (OrderedDomain.ContFunCarrier D E), ∀ hA : A.Nonempty,
        FunctionSpace.PointwiseInfDirectedSupLeast D E A
          (FunctionSpace.nonemptyPointwiseInfCoord hinf A hA)) :
    HasNonemptyInfima (OrderedDomain.functionSpace D E) := by
  exact functionSpace_hasNonemptyInfima_of_pointwiseInfDirectedSup hinf (fun A hA =>
    FunctionSpace.pointwiseInfPreservesDirectedSups_of_least (hleast A hA))

/-- Principal-lower function-space infima follow once the chosen pointwise
infimum functions satisfy the remaining directed-supremum least-upper-bound
half. -/
theorem functionSpace_hasPrincipalLowerInfima_of_pointwiseInfDirectedSupLeast
    {D E : OrderedDomain.{u}} (hinf : HasPrincipalLowerInfima E)
    (hleast :
      ∀ f : OrderedDomain.ContFunCarrier D E,
        ∀ A : Set (OrderedDomain.ContFunCarrier D E),
          ∀ hA : A.Nonempty,
            ∀ hAf : A ⊆ {g : OrderedDomain.ContFunCarrier D E | g ≤ f},
              FunctionSpace.PointwiseInfDirectedSupLeast D E A
                (FunctionSpace.principalLowerPointwiseInfCoord hinf f A hA hAf)) :
    HasPrincipalLowerInfima (OrderedDomain.functionSpace D E) := by
  exact functionSpace_hasPrincipalLowerInfima_of_pointwiseInfDirectedSup hinf
    (fun f A hA hAf =>
      FunctionSpace.pointwiseInfPreservesDirectedSups_of_least (hleast f A hA hAf))

/-- Arbitrary function-space infima follow from the exchange-law formulation. -/
theorem functionSpace_hasAllInfima_of_pointwiseInfDirectedSupExchange
    {D E : OrderedDomain.{u}} (hinf : HasAllInfima E)
    (hexchange :
      ∀ A : Set (OrderedDomain.ContFunCarrier D E),
        FunctionSpace.PointwiseInfDirectedSupExchange D E A
          (FunctionSpace.allPointwiseInfCoord hinf A)) :
    HasAllInfima (OrderedDomain.functionSpace D E) := by
  exact functionSpace_hasAllInfima_of_pointwiseInfDirectedSupLeast hinf (fun A =>
    FunctionSpace.pointwiseInfDirectedSupLeast_of_directedSupExchange (hexchange A))

/-- Nonempty function-space infima follow from the exchange-law formulation. -/
theorem functionSpace_hasNonemptyInfima_of_pointwiseInfDirectedSupExchange
    {D E : OrderedDomain.{u}} (hinf : HasNonemptyInfima E)
    (hexchange :
      ∀ A : Set (OrderedDomain.ContFunCarrier D E), ∀ hA : A.Nonempty,
        FunctionSpace.PointwiseInfDirectedSupExchange D E A
          (FunctionSpace.nonemptyPointwiseInfCoord hinf A hA)) :
    HasNonemptyInfima (OrderedDomain.functionSpace D E) := by
  exact functionSpace_hasNonemptyInfima_of_pointwiseInfDirectedSupLeast hinf (fun A hA =>
    FunctionSpace.pointwiseInfDirectedSupLeast_of_directedSupExchange (hexchange A hA))

/-- Principal-lower function-space infima follow from the exchange-law
formulation. -/
theorem functionSpace_hasPrincipalLowerInfima_of_pointwiseInfDirectedSupExchange
    {D E : OrderedDomain.{u}} (hinf : HasPrincipalLowerInfima E)
    (hexchange :
      ∀ f : OrderedDomain.ContFunCarrier D E,
        ∀ A : Set (OrderedDomain.ContFunCarrier D E),
          ∀ hA : A.Nonempty,
            ∀ hAf : A ⊆ {g : OrderedDomain.ContFunCarrier D E | g ≤ f},
              FunctionSpace.PointwiseInfDirectedSupExchange D E A
                (FunctionSpace.principalLowerPointwiseInfCoord hinf f A hA hAf)) :
    HasPrincipalLowerInfima (OrderedDomain.functionSpace D E) := by
  exact functionSpace_hasPrincipalLowerInfima_of_pointwiseInfDirectedSupLeast hinf
    (fun f A hA hAf =>
      FunctionSpace.pointwiseInfDirectedSupLeast_of_directedSupExchange
        (hexchange f A hA hAf))

/-- Proposition 4.1.5 support data. PDF text: "Let `D` be a continuous domain
and `E` an L-domain (bc-domain, continuous lattice). Then `[D -> E]` is again an L-domain
(bc-domain, continuous lattice)." This data records the genuinely
nontrivial function-space facts needed after the bottom and coordinatewise
infimum choices are handled pointwise. Continuity of the function space and the
local infimum/supremum exchange laws for the chosen pointwise infimum functions
remain supplied as explicit fields. -/
structure LatticeLikeFunctionSpaceData : Prop where
  continuous :
    ∀ {D E : OrderedDomain.{u}}, Chapter3.IsContinuousDomain D.carrier →
      Chapter3.IsContinuousDomain E.carrier →
        Chapter3.IsContinuousDomain (OrderedDomain.functionSpace D E).carrier
  principal_lower_pointwise_infimum_directedSup_exchange :
    ∀ {D E : OrderedDomain.{u}},
      ∀ (hinf : HasPrincipalLowerInfima E)
        (f : OrderedDomain.ContFunCarrier D E)
        (A : Set (OrderedDomain.ContFunCarrier D E))
        (hA : A.Nonempty)
        (hAf : A ⊆ {g : OrderedDomain.ContFunCarrier D E | g ≤ f}),
          FunctionSpace.PointwiseInfDirectedSupExchange D E A
            (FunctionSpace.principalLowerPointwiseInfCoord hinf f A hA hAf)
  nonempty_pointwise_infimum_directedSup_exchange :
    ∀ {D E : OrderedDomain.{u}},
      ∀ (hinf : HasNonemptyInfima E)
        (A : Set (OrderedDomain.ContFunCarrier D E)) (hA : A.Nonempty),
          FunctionSpace.PointwiseInfDirectedSupExchange D E A
            (FunctionSpace.nonemptyPointwiseInfCoord hinf A hA)
  all_pointwise_infimum_directedSup_exchange :
    ∀ {D E : OrderedDomain.{u}},
      ∀ (hinf : HasAllInfima E) (A : Set (OrderedDomain.ContFunCarrier D E)),
        FunctionSpace.PointwiseInfDirectedSupExchange D E A
          (FunctionSpace.allPointwiseInfCoord hinf A)

/-- Step-function sufficient data for Proposition 4.1.5. Compared with
`LatticeLikeFunctionSpaceData`, the function-space continuity component is
not supplied directly: it is derived from explicit dcpo data and the
step-function approximation data. -/
structure LatticeLikeFunctionSpaceStepData where
  continuity_data :
    ∀ {D E : OrderedDomain.{u}}, Chapter3.IsContinuousDomain D.carrier →
      Chapter3.IsContinuousDomain E.carrier →
        FunctionSpace.StepContinuityData D E
  principal_lower_pointwise_infimum_directedSup_exchange :
    ∀ {D E : OrderedDomain.{u}},
      ∀ (hinf : HasPrincipalLowerInfima E)
        (f : OrderedDomain.ContFunCarrier D E)
        (A : Set (OrderedDomain.ContFunCarrier D E))
        (hA : A.Nonempty)
        (hAf : A ⊆ {g : OrderedDomain.ContFunCarrier D E | g ≤ f}),
          FunctionSpace.PointwiseInfDirectedSupExchange D E A
            (FunctionSpace.principalLowerPointwiseInfCoord hinf f A hA hAf)
  nonempty_pointwise_infimum_directedSup_exchange :
    ∀ {D E : OrderedDomain.{u}},
      ∀ (hinf : HasNonemptyInfima E)
        (A : Set (OrderedDomain.ContFunCarrier D E)) (hA : A.Nonempty),
          FunctionSpace.PointwiseInfDirectedSupExchange D E A
            (FunctionSpace.nonemptyPointwiseInfCoord hinf A hA)
  all_pointwise_infimum_directedSup_exchange :
    ∀ {D E : OrderedDomain.{u}},
      ∀ (hinf : HasAllInfima E) (A : Set (OrderedDomain.ContFunCarrier D E)),
        FunctionSpace.PointwiseInfDirectedSupExchange D E A
          (FunctionSpace.allPointwiseInfCoord hinf A)

/-- The step-function sufficient data gives the current function-space data by
proving the continuity field from `StepContinuityData`. -/
theorem latticeLikeFunctionSpaceData_of_stepData
    (hStep : LatticeLikeFunctionSpaceStepData.{u}) :
    LatticeLikeFunctionSpaceData.{u} := by
  constructor
  · intro D E hD hE
    exact FunctionSpace.continuousDomain_of_stepContinuityData hD hE
      (hStep.continuity_data hD hE)
  · exact hStep.principal_lower_pointwise_infimum_directedSup_exchange
  · exact hStep.nonempty_pointwise_infimum_directedSup_exchange
  · exact hStep.all_pointwise_infimum_directedSup_exchange

/-- A strong sufficient data package for Proposition 4.1.5: instead of directly
supplying the least-upper-bound half of directed-supremum preservation, it
supplies an upper adjoint for each chosen raw pointwise-infimum map. The PDF
states Proposition 4.1.5 here without proof, so this is recorded only as a
sufficient route, not as the extracted proof. -/
structure LatticeLikeFunctionSpaceAdjointSufficientData : Prop where
  continuous :
    ∀ {D E : OrderedDomain.{u}}, Chapter3.IsContinuousDomain D.carrier →
      Chapter3.IsContinuousDomain E.carrier →
        Chapter3.IsContinuousDomain (OrderedDomain.functionSpace D E).carrier
  principal_lower_pointwise_infimum_hasUpperAdjoint :
    ∀ {D E : OrderedDomain.{u}},
      ∀ (hinf : HasPrincipalLowerInfima E)
        (f : OrderedDomain.ContFunCarrier D E)
        (A : Set (OrderedDomain.ContFunCarrier D E))
        (hA : A.Nonempty)
        (hAf : A ⊆ {g : OrderedDomain.ContFunCarrier D E | g ≤ f}),
          Chapter3.HasUpperAdjoint
            (FunctionSpace.pointwiseInfFun D E A
              (FunctionSpace.principalLowerPointwiseInfCoord hinf f A hA hAf))
  nonempty_pointwise_infimum_hasUpperAdjoint :
    ∀ {D E : OrderedDomain.{u}},
      ∀ (hinf : HasNonemptyInfima E)
        (A : Set (OrderedDomain.ContFunCarrier D E)) (hA : A.Nonempty),
          Chapter3.HasUpperAdjoint
            (FunctionSpace.pointwiseInfFun D E A
              (FunctionSpace.nonemptyPointwiseInfCoord hinf A hA))
  all_pointwise_infimum_hasUpperAdjoint :
    ∀ {D E : OrderedDomain.{u}},
      ∀ (hinf : HasAllInfima E) (A : Set (OrderedDomain.ContFunCarrier D E)),
        Chapter3.HasUpperAdjoint
          (FunctionSpace.pointwiseInfFun D E A
            (FunctionSpace.allPointwiseInfCoord hinf A))

/-- Concrete-data version of the adjoint-sufficient data for Proposition
4.1.5. Each field returns data containing a specific proposed upper map,
packaged through `PointwiseInfUpperAdjointData`, rather than only existential
`HasUpperAdjoint` data. -/
structure LatticeLikeFunctionSpaceAdjointWitnessData where
  continuous :
    ∀ {D E : OrderedDomain.{u}}, Chapter3.IsContinuousDomain D.carrier →
      Chapter3.IsContinuousDomain E.carrier →
        Chapter3.IsContinuousDomain (OrderedDomain.functionSpace D E).carrier
  principal_lower_pointwise_infimum_adjointData :
    ∀ {D E : OrderedDomain.{u}},
      ∀ (hinf : HasPrincipalLowerInfima E)
        (f : OrderedDomain.ContFunCarrier D E)
        (A : Set (OrderedDomain.ContFunCarrier D E))
        (hA : A.Nonempty)
        (hAf : A ⊆ {g : OrderedDomain.ContFunCarrier D E | g ≤ f}),
          FunctionSpace.PointwiseInfUpperAdjointData D E A
            (FunctionSpace.principalLowerPointwiseInfCoord hinf f A hA hAf)
  nonempty_pointwise_infimum_adjointData :
    ∀ {D E : OrderedDomain.{u}},
      ∀ (hinf : HasNonemptyInfima E)
        (A : Set (OrderedDomain.ContFunCarrier D E)) (hA : A.Nonempty),
          FunctionSpace.PointwiseInfUpperAdjointData D E A
            (FunctionSpace.nonemptyPointwiseInfCoord hinf A hA)
  all_pointwise_infimum_adjointData :
    ∀ {D E : OrderedDomain.{u}},
      ∀ (hinf : HasAllInfima E) (A : Set (OrderedDomain.ContFunCarrier D E)),
        FunctionSpace.PointwiseInfUpperAdjointData D E A
          (FunctionSpace.allPointwiseInfCoord hinf A)

/-- Fully concrete sufficient data currently recorded for Proposition
4.1.5. Continuity is supplied by explicit step-function data, while the
pointwise-infimum exchange laws are supplied by concrete upper-adjoint data.
This remains sufficient data, not a construction of those data from the
PDF's base hypotheses. -/
structure LatticeLikeFunctionSpaceStepAdjointWitnessData where
  continuity_data :
    ∀ {D E : OrderedDomain.{u}}, Chapter3.IsContinuousDomain D.carrier →
      Chapter3.IsContinuousDomain E.carrier →
        FunctionSpace.StepContinuityData D E
  principal_lower_pointwise_infimum_adjointData :
    ∀ {D E : OrderedDomain.{u}},
      ∀ (hinf : HasPrincipalLowerInfima E)
        (f : OrderedDomain.ContFunCarrier D E)
        (A : Set (OrderedDomain.ContFunCarrier D E))
        (hA : A.Nonempty)
        (hAf : A ⊆ {g : OrderedDomain.ContFunCarrier D E | g ≤ f}),
          FunctionSpace.PointwiseInfUpperAdjointData D E A
            (FunctionSpace.principalLowerPointwiseInfCoord hinf f A hA hAf)
  nonempty_pointwise_infimum_adjointData :
    ∀ {D E : OrderedDomain.{u}},
      ∀ (hinf : HasNonemptyInfima E)
        (A : Set (OrderedDomain.ContFunCarrier D E)) (hA : A.Nonempty),
          FunctionSpace.PointwiseInfUpperAdjointData D E A
            (FunctionSpace.nonemptyPointwiseInfCoord hinf A hA)
  all_pointwise_infimum_adjointData :
    ∀ {D E : OrderedDomain.{u}},
      ∀ (hinf : HasAllInfima E) (A : Set (OrderedDomain.ContFunCarrier D E)),
        FunctionSpace.PointwiseInfUpperAdjointData D E A
          (FunctionSpace.allPointwiseInfCoord hinf A)

/-- Least-member sufficient data for Proposition 4.1.5.  It records a
continuity route for function spaces plus actual least-function witnesses for
the nonempty pointwise families that occur in the L-domain and bc-domain
infimum clauses.  The continuous-lattice empty-family case is handled from the
codomain's arbitrary-infimum hypothesis. -/
structure LatticeLikeFunctionSpaceLeastMemberData where
  continuous :
    ∀ {D E : OrderedDomain.{u}}, Chapter3.IsContinuousDomain D.carrier →
      Chapter3.IsContinuousDomain E.carrier →
        Chapter3.IsContinuousDomain (OrderedDomain.functionSpace D E).carrier
  principal_lower_leastMember :
    ∀ {D E : OrderedDomain.{u}},
      ∀ (f : OrderedDomain.ContFunCarrier D E)
        (A : Set (OrderedDomain.ContFunCarrier D E))
        (_hA : A.Nonempty)
        (_hAf : A ⊆ {g : OrderedDomain.ContFunCarrier D E | g ≤ f}),
          FunctionSpace.LeastMemberData D E A
  nonempty_leastMember :
    ∀ {D E : OrderedDomain.{u}},
      ∀ (A : Set (OrderedDomain.ContFunCarrier D E)) (_hA : A.Nonempty),
        FunctionSpace.LeastMemberData D E A

/-- The concrete step-plus-adjoint witness data gives the step-function
sufficient data. -/
def latticeLikeFunctionSpaceStepData_of_stepAdjointWitnessData
    (hData : LatticeLikeFunctionSpaceStepAdjointWitnessData.{u}) :
    LatticeLikeFunctionSpaceStepData.{u} := by
  constructor
  · exact hData.continuity_data
  · intro D E hinf f A hA hAf
    exact FunctionSpace.pointwiseInfDirectedSupExchange_of_upperAdjointData
      (hData.principal_lower_pointwise_infimum_adjointData hinf f A hA hAf)
  · intro D E hinf A hA
    exact FunctionSpace.pointwiseInfDirectedSupExchange_of_upperAdjointData
      (hData.nonempty_pointwise_infimum_adjointData hinf A hA)
  · intro D E hinf A
    exact FunctionSpace.pointwiseInfDirectedSupExchange_of_upperAdjointData
      (hData.all_pointwise_infimum_adjointData hinf A)

/-- The concrete step-plus-adjoint witness data also gives the concrete adjoint
witness data by deriving its continuity field from
step-continuity data. -/
def latticeLikeFunctionSpaceAdjointWitnessData_of_stepAdjointWitnessData
    (hData : LatticeLikeFunctionSpaceStepAdjointWitnessData.{u}) :
    LatticeLikeFunctionSpaceAdjointWitnessData.{u} := by
  constructor
  · intro D E hD hE
    exact FunctionSpace.continuousDomain_of_stepContinuityData hD hE
      (hData.continuity_data hD hE)
  · exact hData.principal_lower_pointwise_infimum_adjointData
  · exact hData.nonempty_pointwise_infimum_adjointData
  · exact hData.all_pointwise_infimum_adjointData

/-- The concrete adjoint witness data gives the existential adjoint sufficient data. -/
theorem latticeLikeFunctionSpaceAdjointSufficientData_of_adjointWitnessData
    (hData : LatticeLikeFunctionSpaceAdjointWitnessData.{u}) :
    LatticeLikeFunctionSpaceAdjointSufficientData.{u} := by
  constructor
  · exact hData.continuous
  · intro D E hinf f A hA hAf
    exact FunctionSpace.pointwiseInfHasUpperAdjoint_of_upperAdjointData
      (hData.principal_lower_pointwise_infimum_adjointData hinf f A hA hAf)
  · intro D E hinf A hA
    exact FunctionSpace.pointwiseInfHasUpperAdjoint_of_upperAdjointData
      (hData.nonempty_pointwise_infimum_adjointData hinf A hA)
  · intro D E hinf A
    exact FunctionSpace.pointwiseInfHasUpperAdjoint_of_upperAdjointData
      (hData.all_pointwise_infimum_adjointData hinf A)

/-- The adjoint-based sufficient data gives the current exchange-law
function-space data. -/
theorem latticeLikeFunctionSpaceData_of_adjointSufficientData
    (hAdjoint : LatticeLikeFunctionSpaceAdjointSufficientData.{u}) :
    LatticeLikeFunctionSpaceData.{u} := by
  constructor
  · exact hAdjoint.continuous
  · intro D E hinf f A hA hAf
    exact FunctionSpace.pointwiseInfDirectedSupExchange_of_hasUpperAdjoint
      (FunctionSpace.principalLowerPointwiseInfCoord hinf f A hA hAf)
      (hAdjoint.principal_lower_pointwise_infimum_hasUpperAdjoint hinf f A hA hAf)
  · intro D E hinf A hA
    exact FunctionSpace.pointwiseInfDirectedSupExchange_of_hasUpperAdjoint
      (FunctionSpace.nonemptyPointwiseInfCoord hinf A hA)
      (hAdjoint.nonempty_pointwise_infimum_hasUpperAdjoint hinf A hA)
  · intro D E hinf A
    exact FunctionSpace.pointwiseInfDirectedSupExchange_of_hasUpperAdjoint
      (FunctionSpace.allPointwiseInfCoord hinf A)
      (hAdjoint.all_pointwise_infimum_hasUpperAdjoint hinf A)

/-- The concrete adjoint witness data also gives the current exchange-law
function-space data. -/
theorem latticeLikeFunctionSpaceData_of_adjointWitnessData
    (hData : LatticeLikeFunctionSpaceAdjointWitnessData.{u}) :
    LatticeLikeFunctionSpaceData.{u} :=
  latticeLikeFunctionSpaceData_of_adjointSufficientData
    (latticeLikeFunctionSpaceAdjointSufficientData_of_adjointWitnessData hData)

/-- Proposition 4.1.5 auxiliary exchange-law data form. PDF text: "Let `D` be a continuous domain and `E` an
L-domain (bc-domain, continuous lattice). Then `[D -> E]` is again an L-domain
(bc-domain, continuous lattice)." Data form: function spaces into
lattice-like domains preserve the lattice-like class. The bottom component is
proved pointwise; the remaining function-space continuity and infimum-closure
facts are supplied by the explicit function-space data. -/
theorem prop_4_1_5_function_spaces_lattice_like_of_data
    {D E : OrderedDomain.{u}} (hD : Chapter3.IsContinuousDomain D.carrier)
    (hData : LatticeLikeFunctionSpaceData.{u}) :
    (IsLDomain E → IsLDomain (OrderedDomain.functionSpace D E)) ∧
      (IsBcDomain E → IsBcDomain (OrderedDomain.functionSpace D E)) ∧
      (IsContinuousLatticeDomain E →
        IsContinuousLatticeDomain (OrderedDomain.functionSpace D E)) := by
  constructor
  · intro hE
    rcases hE with ⟨hbotE, hcontE, hinfE⟩
    exact ⟨functionSpace_hasBottom_of_codomain D E hbotE,
      hData.continuous hD hcontE,
      functionSpace_hasPrincipalLowerInfima_of_pointwiseInfDirectedSupExchange hinfE
        (hData.principal_lower_pointwise_infimum_directedSup_exchange hinfE)⟩
  constructor
  · intro hE
    rcases hE with ⟨hbotE, hcontE, hinfE⟩
    exact ⟨functionSpace_hasBottom_of_codomain D E hbotE,
      hData.continuous hD hcontE,
      functionSpace_hasNonemptyInfima_of_pointwiseInfDirectedSupExchange hinfE
        (hData.nonempty_pointwise_infimum_directedSup_exchange hinfE)⟩
  · intro hE
    rcases hE with ⟨hbotE, hcontE, hinfE⟩
    exact ⟨functionSpace_hasBottom_of_codomain D E hbotE,
      hData.continuous hD hcontE,
      functionSpace_hasAllInfima_of_pointwiseInfDirectedSupExchange hinfE
        (hData.all_pointwise_infimum_directedSup_exchange hinfE)⟩

/-- Proposition 4.1.5, least-member sufficient form: function spaces preserve
the lattice-like classes when continuity is supplied and the relevant nonempty
function families have actual least members.  The all-infima branch handles the
empty family by using the codomain's empty infimum as the pointwise top. -/
theorem prop_4_1_5_function_spaces_lattice_like_of_leastMemberData
    {D E : OrderedDomain.{u}} (hD : Chapter3.IsContinuousDomain D.carrier)
    (hData : LatticeLikeFunctionSpaceLeastMemberData.{u}) :
    (IsLDomain E → IsLDomain (OrderedDomain.functionSpace D E)) ∧
      (IsBcDomain E → IsBcDomain (OrderedDomain.functionSpace D E)) ∧
      (IsContinuousLatticeDomain E →
        IsContinuousLatticeDomain (OrderedDomain.functionSpace D E)) := by
  constructor
  · intro hE
    rcases hE with ⟨hbotE, hcontE, _hinfE⟩
    exact ⟨functionSpace_hasBottom_of_codomain D E hbotE,
      hData.continuous hD hcontE,
      functionSpace_hasPrincipalLowerInfima_of_leastMembers
        hData.principal_lower_leastMember⟩
  constructor
  · intro hE
    rcases hE with ⟨hbotE, hcontE, _hinfE⟩
    exact ⟨functionSpace_hasBottom_of_codomain D E hbotE,
      hData.continuous hD hcontE,
      functionSpace_hasNonemptyInfima_of_leastMembers
        hData.nonempty_leastMember⟩
  · intro hE
    rcases hE with ⟨hbotE, hcontE, hinfE⟩
    exact ⟨functionSpace_hasBottom_of_codomain D E hbotE,
      hData.continuous hD hcontE,
      functionSpace_hasAllInfima_of_nonemptyLeastMembers hinfE
        hData.nonempty_leastMember⟩

/-- Proposition 4.1.5, PDF text: "Let `D` be a continuous domain and `E` an
L-domain (bc-domain, continuous lattice). Then `[D -> E]` is again an L-domain
(bc-domain, continuous lattice)."  The PDF gives no local proof of the
function-space continuity and pointwise-infimum exchange laws in this paragraph,
so the direct numbered theorem is registered as local proof debt. -/
theorem prop_4_1_5_function_spaces_lattice_like
    {D E : OrderedDomain.{u}} (hD : Chapter3.IsContinuousDomain D.carrier) :
    (IsLDomain E → IsLDomain (OrderedDomain.functionSpace D E)) ∧
      (IsBcDomain E → IsBcDomain (OrderedDomain.functionSpace D E)) ∧
      (IsContinuousLatticeDomain E →
        IsContinuousLatticeDomain (OrderedDomain.functionSpace D E)) := by
  admit

/-- Proposition 4.1.5, step-function sufficient form: the same lattice-like
function-space closure follows when the continuity component is supplied by
explicit dcpo data and the step-function approximation principle. -/
theorem prop_4_1_5_function_spaces_lattice_like_of_step
    {D E : OrderedDomain.{u}} (hD : Chapter3.IsContinuousDomain D.carrier)
    (hStep : LatticeLikeFunctionSpaceStepData.{u}) :
    (IsLDomain E → IsLDomain (OrderedDomain.functionSpace D E)) ∧
      (IsBcDomain E → IsBcDomain (OrderedDomain.functionSpace D E)) ∧
      (IsContinuousLatticeDomain E →
        IsContinuousLatticeDomain (OrderedDomain.functionSpace D E)) := by
  exact prop_4_1_5_function_spaces_lattice_like_of_data hD
    (latticeLikeFunctionSpaceData_of_stepData hStep)

/-- Proposition 4.1.5, concrete step-plus-adjoint-data sufficient form. This
packages both current sufficient routes: step functions provide continuity, and
upper-adjoint data provides the remaining pointwise-infimum exchange laws. -/
theorem prop_4_1_5_function_spaces_lattice_like_of_stepAdjointData
    {D E : OrderedDomain.{u}} (hD : Chapter3.IsContinuousDomain D.carrier)
    (hData : LatticeLikeFunctionSpaceStepAdjointWitnessData.{u}) :
    (IsLDomain E → IsLDomain (OrderedDomain.functionSpace D E)) ∧
      (IsBcDomain E → IsBcDomain (OrderedDomain.functionSpace D E)) ∧
      (IsContinuousLatticeDomain E →
        IsContinuousLatticeDomain (OrderedDomain.functionSpace D E)) := by
  exact prop_4_1_5_function_spaces_lattice_like_of_step hD
    (latticeLikeFunctionSpaceStepData_of_stepAdjointWitnessData hData)

/-- Proposition 4.1.5, adjoint-sufficient form: the same lattice-like
function-space closure follows from the strong adjoint-based sufficient
data. -/
theorem prop_4_1_5_function_spaces_lattice_like_of_adjoint
    {D E : OrderedDomain.{u}} (hD : Chapter3.IsContinuousDomain D.carrier)
    (hAdjoint : LatticeLikeFunctionSpaceAdjointSufficientData.{u}) :
    (IsLDomain E → IsLDomain (OrderedDomain.functionSpace D E)) ∧
      (IsBcDomain E → IsBcDomain (OrderedDomain.functionSpace D E)) ∧
      (IsContinuousLatticeDomain E →
        IsContinuousLatticeDomain (OrderedDomain.functionSpace D E)) := by
  exact prop_4_1_5_function_spaces_lattice_like_of_data hD
    (latticeLikeFunctionSpaceData_of_adjointSufficientData hAdjoint)

/-- Proposition 4.1.5, concrete-adjoint-data sufficient form. This is the same
conditional conclusion as the adjoint-sufficient form, with each adjoint carried
by an explicit upper map. -/
theorem prop_4_1_5_function_spaces_lattice_like_of_adjointData
    {D E : OrderedDomain.{u}} (hD : Chapter3.IsContinuousDomain D.carrier)
    (hData : LatticeLikeFunctionSpaceAdjointWitnessData.{u}) :
    (IsLDomain E → IsLDomain (OrderedDomain.functionSpace D E)) ∧
      (IsBcDomain E → IsBcDomain (OrderedDomain.functionSpace D E)) ∧
      (IsContinuousLatticeDomain E →
        IsContinuousLatticeDomain (OrderedDomain.functionSpace D E)) := by
  exact prop_4_1_5_function_spaces_lattice_like_of_adjoint hD
    (latticeLikeFunctionSpaceAdjointSufficientData_of_adjointWitnessData hData)

/-- The Chapter 4 class of L-domains. -/
def LDomainClass : DomainClass.{u} where
  Obj := IsLDomain

/-- The Chapter 4 class of bc-domains. -/
def BcDomainClass : DomainClass.{u} where
  Obj := IsBcDomain

/-- The Chapter 4 class of continuous lattices. -/
def ContinuousLatticeDomainClass : DomainClass.{u} where
  Obj := IsContinuousLatticeDomain

/-- The Chapter 4 algebraic counterpart `aL` of L-domains. -/
def AlgebraicLDomainClass : DomainClass.{u} where
  Obj := fun D => IsLDomain D ∧ Chapter3.IsAlgebraicDomain D.carrier

/-- The Chapter 4 algebraic counterpart `aBC` of bc-domains. -/
def AlgebraicBcDomainClass : DomainClass.{u} where
  Obj := fun D => IsBcDomain D ∧ Chapter3.IsAlgebraicDomain D.carrier

/-- The Chapter 4 algebraic counterpart `aLAT` of continuous lattices. -/
def AlgebraicContinuousLatticeDomainClass : DomainClass.{u} where
  Obj := fun D => IsContinuousLatticeDomain D ∧ Chapter3.IsAlgebraicDomain D.carrier

/-- Corollary 4.1.6, PDF text: "The categories L, BC, LAT, and their algebraic
counterparts are cartesian closed." Algebraic-counterpart data package: the
algebraic lattice-like categories are cartesian closed. -/
structure AlgebraicLatticeLikeCartesianClosedData : Prop where
  cartesian_closed :
    DomainClass.CartesianClosed (AlgebraicLDomainClass : DomainClass.{u}) ∧
      DomainClass.CartesianClosed (AlgebraicBcDomainClass : DomainClass.{u}) ∧
        DomainClass.CartesianClosed
          (AlgebraicContinuousLatticeDomainClass : DomainClass.{u})

/-- Corollary 4.1.6 auxiliary function-space-data form. PDF text: "The categories L, BC, LAT, and their algebraic
counterparts are cartesian closed." Auxiliary partial package form: the three
continuous lattice-like classes are cartesian closed; the function-space part
depends on the explicit data from Proposition 4.1.5. -/
theorem cor_4_1_6_lattice_like_categories_cartesian_closed_of_functionSpaceData
    (hData : LatticeLikeFunctionSpaceData.{u}) :
    DomainClass.CartesianClosed (LDomainClass : DomainClass.{u}) ∧
      DomainClass.CartesianClosed (BcDomainClass : DomainClass.{u}) ∧
      DomainClass.CartesianClosed (ContinuousLatticeDomainClass : DomainClass.{u}) := by
  have hProdL : DomainClass.ClosedUnderProducts LDomainClass := by
    intro D E hD hE
    rcases hD with ⟨hbotD, hcontD, hinfD⟩
    rcases hE with ⟨hbotE, hcontE, hinfE⟩
    constructor
    · rcases hbotD with ⟨botD, hbotD⟩
      rcases hbotE with ⟨botE, hbotE⟩
      exact ⟨(botD, botE), by
        intro x
        exact ⟨hbotD x.1, hbotE x.2⟩⟩
    constructor
    · simpa [OrderedDomain.prod] using Chapter3.prod_continuous_domain hcontD hcontE
    · intro x A hAne hAprincipal
      have hFstNonempty : (Prod.fst '' A).Nonempty := hAne.image Prod.fst
      have hSndNonempty : (Prod.snd '' A).Nonempty := hAne.image Prod.snd
      have hFstPrincipal : Prod.fst '' A ⊆ {y : D.carrier | y ≤ x.1} := by
        intro y hy
        rcases hy with ⟨a, ha, rfl⟩
        exact (hAprincipal ha).1
      have hSndPrincipal : Prod.snd '' A ⊆ {y : E.carrier | y ≤ x.2} := by
        intro y hy
        rcases hy with ⟨a, ha, rfl⟩
        exact (hAprincipal ha).2
      rcases hinfD x.1 (Prod.fst '' A) hFstNonempty hFstPrincipal with ⟨iD, hiD⟩
      rcases hinfE x.2 (Prod.snd '' A) hSndNonempty hSndPrincipal with ⟨iE, hiE⟩
      refine ⟨(iD, iE), ?_⟩
      constructor
      · intro a ha
        exact ⟨hiD.1 ⟨a, ha, rfl⟩, hiE.1 ⟨a, ha, rfl⟩⟩
      · intro y hy
        constructor
        · exact hiD.2 y.1 (by
            intro d hd
            rcases hd with ⟨a, ha, rfl⟩
            exact (hy ha).1)
        · exact hiE.2 y.2 (by
            intro e he
            rcases he with ⟨a, ha, rfl⟩
            exact (hy ha).2)
  have hProdBc : DomainClass.ClosedUnderProducts BcDomainClass := by
    intro D E hD hE
    rcases hD with ⟨hbotD, hcontD, hinfD⟩
    rcases hE with ⟨hbotE, hcontE, hinfE⟩
    constructor
    · rcases hbotD with ⟨botD, hbotD⟩
      rcases hbotE with ⟨botE, hbotE⟩
      exact ⟨(botD, botE), by
        intro x
        exact ⟨hbotD x.1, hbotE x.2⟩⟩
    constructor
    · simpa [OrderedDomain.prod] using Chapter3.prod_continuous_domain hcontD hcontE
    · intro A hAne
      have hFstNonempty : (Prod.fst '' A).Nonempty := hAne.image Prod.fst
      have hSndNonempty : (Prod.snd '' A).Nonempty := hAne.image Prod.snd
      rcases hinfD (Prod.fst '' A) hFstNonempty with ⟨iD, hiD⟩
      rcases hinfE (Prod.snd '' A) hSndNonempty with ⟨iE, hiE⟩
      refine ⟨(iD, iE), ?_⟩
      constructor
      · intro a ha
        exact ⟨hiD.1 ⟨a, ha, rfl⟩, hiE.1 ⟨a, ha, rfl⟩⟩
      · intro y hy
        constructor
        · exact hiD.2 y.1 (by
            intro d hd
            rcases hd with ⟨a, ha, rfl⟩
            exact (hy ha).1)
        · exact hiE.2 y.2 (by
            intro e he
            rcases he with ⟨a, ha, rfl⟩
            exact (hy ha).2)
  have hProdCL : DomainClass.ClosedUnderProducts ContinuousLatticeDomainClass := by
    intro D E hD hE
    rcases hD with ⟨hbotD, hcontD, hinfD⟩
    rcases hE with ⟨hbotE, hcontE, hinfE⟩
    constructor
    · rcases hbotD with ⟨botD, hbotD⟩
      rcases hbotE with ⟨botE, hbotE⟩
      exact ⟨(botD, botE), by
        intro x
        exact ⟨hbotD x.1, hbotE x.2⟩⟩
    constructor
    · simpa [OrderedDomain.prod] using Chapter3.prod_continuous_domain hcontD hcontE
    · intro A
      rcases hinfD (Prod.fst '' A) with ⟨iD, hiD⟩
      rcases hinfE (Prod.snd '' A) with ⟨iE, hiE⟩
      refine ⟨(iD, iE), ?_⟩
      constructor
      · intro a ha
        exact ⟨hiD.1 ⟨a, ha, rfl⟩, hiE.1 ⟨a, ha, rfl⟩⟩
      · intro y hy
        constructor
        · exact hiD.2 y.1 (by
            intro d hd
            rcases hd with ⟨a, ha, rfl⟩
            exact (hy ha).1)
        · exact hiE.2 y.2 (by
            intro e he
            rcases he with ⟨a, ha, rfl⟩
            exact (hy ha).2)
  have hFunL : DomainClass.ClosedUnderFunctionSpaces LDomainClass := by
    intro D E hD hE
    exact (prop_4_1_5_function_spaces_lattice_like_of_data
      (D := D) (E := E) hD.2.1 hData).1 hE
  have hFunBc : DomainClass.ClosedUnderFunctionSpaces BcDomainClass := by
    intro D E hD hE
    exact (prop_4_1_5_function_spaces_lattice_like_of_data
      (D := D) (E := E) hD.2.1 hData).2.1 hE
  have hFunCL : DomainClass.ClosedUnderFunctionSpaces ContinuousLatticeDomainClass := by
    intro D E hD hE
    exact (prop_4_1_5_function_spaces_lattice_like_of_data
      (D := D) (E := E) hD.2.1 hData).2.2 hE
  exact ⟨⟨hProdL, hFunL⟩, ⟨hProdBc, hFunBc⟩, ⟨hProdCL, hFunCL⟩⟩

/-- Product closure for the three continuous lattice-like domain classes. -/
theorem latticeLike_product_closures :
    DomainClass.ClosedUnderProducts (LDomainClass : DomainClass.{u}) ∧
      DomainClass.ClosedUnderProducts (BcDomainClass : DomainClass.{u}) ∧
        DomainClass.ClosedUnderProducts
          (ContinuousLatticeDomainClass : DomainClass.{u}) := by
  have hProdL : DomainClass.ClosedUnderProducts LDomainClass := by
    intro D E hD hE
    rcases hD with ⟨hbotD, hcontD, hinfD⟩
    rcases hE with ⟨hbotE, hcontE, hinfE⟩
    constructor
    · rcases hbotD with ⟨botD, hbotD⟩
      rcases hbotE with ⟨botE, hbotE⟩
      exact ⟨(botD, botE), by
        intro x
        exact ⟨hbotD x.1, hbotE x.2⟩⟩
    constructor
    · simpa [OrderedDomain.prod] using Chapter3.prod_continuous_domain hcontD hcontE
    · intro x A hAne hAprincipal
      have hFstNonempty : (Prod.fst '' A).Nonempty := hAne.image Prod.fst
      have hSndNonempty : (Prod.snd '' A).Nonempty := hAne.image Prod.snd
      have hFstPrincipal : Prod.fst '' A ⊆ {y : D.carrier | y ≤ x.1} := by
        intro y hy
        rcases hy with ⟨a, ha, rfl⟩
        exact (hAprincipal ha).1
      have hSndPrincipal : Prod.snd '' A ⊆ {y : E.carrier | y ≤ x.2} := by
        intro y hy
        rcases hy with ⟨a, ha, rfl⟩
        exact (hAprincipal ha).2
      rcases hinfD x.1 (Prod.fst '' A) hFstNonempty hFstPrincipal with ⟨iD, hiD⟩
      rcases hinfE x.2 (Prod.snd '' A) hSndNonempty hSndPrincipal with ⟨iE, hiE⟩
      refine ⟨(iD, iE), ?_⟩
      constructor
      · intro a ha
        exact ⟨hiD.1 ⟨a, ha, rfl⟩, hiE.1 ⟨a, ha, rfl⟩⟩
      · intro y hy
        constructor
        · exact hiD.2 y.1 (by
            intro d hd
            rcases hd with ⟨a, ha, rfl⟩
            exact (hy ha).1)
        · exact hiE.2 y.2 (by
            intro e he
            rcases he with ⟨a, ha, rfl⟩
            exact (hy ha).2)
  have hProdBc : DomainClass.ClosedUnderProducts BcDomainClass := by
    intro D E hD hE
    rcases hD with ⟨hbotD, hcontD, hinfD⟩
    rcases hE with ⟨hbotE, hcontE, hinfE⟩
    constructor
    · rcases hbotD with ⟨botD, hbotD⟩
      rcases hbotE with ⟨botE, hbotE⟩
      exact ⟨(botD, botE), by
        intro x
        exact ⟨hbotD x.1, hbotE x.2⟩⟩
    constructor
    · simpa [OrderedDomain.prod] using Chapter3.prod_continuous_domain hcontD hcontE
    · intro A hAne
      have hFstNonempty : (Prod.fst '' A).Nonempty := hAne.image Prod.fst
      have hSndNonempty : (Prod.snd '' A).Nonempty := hAne.image Prod.snd
      rcases hinfD (Prod.fst '' A) hFstNonempty with ⟨iD, hiD⟩
      rcases hinfE (Prod.snd '' A) hSndNonempty with ⟨iE, hiE⟩
      refine ⟨(iD, iE), ?_⟩
      constructor
      · intro a ha
        exact ⟨hiD.1 ⟨a, ha, rfl⟩, hiE.1 ⟨a, ha, rfl⟩⟩
      · intro y hy
        constructor
        · exact hiD.2 y.1 (by
            intro d hd
            rcases hd with ⟨a, ha, rfl⟩
            exact (hy ha).1)
        · exact hiE.2 y.2 (by
            intro e he
            rcases he with ⟨a, ha, rfl⟩
            exact (hy ha).2)
  have hProdCL : DomainClass.ClosedUnderProducts ContinuousLatticeDomainClass := by
    intro D E hD hE
    rcases hD with ⟨hbotD, hcontD, hinfD⟩
    rcases hE with ⟨hbotE, hcontE, hinfE⟩
    constructor
    · rcases hbotD with ⟨botD, hbotD⟩
      rcases hbotE with ⟨botE, hbotE⟩
      exact ⟨(botD, botE), by
        intro x
        exact ⟨hbotD x.1, hbotE x.2⟩⟩
    constructor
    · simpa [OrderedDomain.prod] using Chapter3.prod_continuous_domain hcontD hcontE
    · intro A
      rcases hinfD (Prod.fst '' A) with ⟨iD, hiD⟩
      rcases hinfE (Prod.snd '' A) with ⟨iE, hiE⟩
      refine ⟨(iD, iE), ?_⟩
      constructor
      · intro a ha
        exact ⟨hiD.1 ⟨a, ha, rfl⟩, hiE.1 ⟨a, ha, rfl⟩⟩
      · intro y hy
        constructor
        · exact hiD.2 y.1 (by
            intro d hd
            rcases hd with ⟨a, ha, rfl⟩
            exact (hy ha).1)
        · exact hiE.2 y.2 (by
            intro e he
            rcases he with ⟨a, ha, rfl⟩
            exact (hy ha).2)
  exact ⟨hProdL, hProdBc, hProdCL⟩

/-- Product closure for the algebraic lattice-like domain classes.  The
lattice-like component is coordinatewise, and the algebraic component is the
Chapter 3 product algebraicity theorem. -/
theorem algebraicLatticeLike_product_closures :
    DomainClass.ClosedUnderProducts (AlgebraicLDomainClass : DomainClass.{u}) ∧
      DomainClass.ClosedUnderProducts (AlgebraicBcDomainClass : DomainClass.{u}) ∧
        DomainClass.ClosedUnderProducts
          (AlgebraicContinuousLatticeDomainClass : DomainClass.{u}) := by
  rcases latticeLike_product_closures with ⟨hProdL, hProdBc, hProdCL⟩
  have hProdAlgL : DomainClass.ClosedUnderProducts AlgebraicLDomainClass := by
    intro D E hD hE
    exact ⟨hProdL hD.1 hE.1,
      by
        simpa [OrderedDomain.prod] using
          Chapter3.prod_algebraic_domain hD.2 hE.2⟩
  have hProdAlgBc : DomainClass.ClosedUnderProducts AlgebraicBcDomainClass := by
    intro D E hD hE
    exact ⟨hProdBc hD.1 hE.1,
      by
        simpa [OrderedDomain.prod] using
          Chapter3.prod_algebraic_domain hD.2 hE.2⟩
  have hProdAlgCL :
      DomainClass.ClosedUnderProducts AlgebraicContinuousLatticeDomainClass := by
    intro D E hD hE
    exact ⟨hProdCL hD.1 hE.1,
      by
        simpa [OrderedDomain.prod] using
          Chapter3.prod_algebraic_domain hD.2 hE.2⟩
  exact ⟨hProdAlgL, hProdAlgBc, hProdAlgCL⟩

/-- Corollary 4.1.6, continuous lattice-like part.  This direct numbered
statement no longer takes a function-space principle as an argument; the
unproved function-space component is registered as local proof debt in
Proposition 4.1.5. -/
theorem cor_4_1_6_lattice_like_categories_cartesian_closed :
    DomainClass.CartesianClosed (LDomainClass : DomainClass.{u}) ∧
      DomainClass.CartesianClosed (BcDomainClass : DomainClass.{u}) ∧
      DomainClass.CartesianClosed (ContinuousLatticeDomainClass : DomainClass.{u}) := by
  rcases latticeLike_product_closures with ⟨hProdL, hProdBc, hProdCL⟩
  have hFunL : DomainClass.ClosedUnderFunctionSpaces LDomainClass := by
    intro D E hD hE
    exact (prop_4_1_5_function_spaces_lattice_like
      (D := D) (E := E) hD.2.1).1 hE
  have hFunBc : DomainClass.ClosedUnderFunctionSpaces BcDomainClass := by
    intro D E hD hE
    exact (prop_4_1_5_function_spaces_lattice_like
      (D := D) (E := E) hD.2.1).2.1 hE
  have hFunCL : DomainClass.ClosedUnderFunctionSpaces ContinuousLatticeDomainClass := by
    intro D E hD hE
    exact (prop_4_1_5_function_spaces_lattice_like
      (D := D) (E := E) hD.2.1).2.2 hE
  exact ⟨⟨hProdL, hFunL⟩, ⟨hProdBc, hFunBc⟩, ⟨hProdCL, hFunCL⟩⟩

/-- Corollary 4.1.6, algebraic counterpart clause: the categories `aL`,
`aBC`, and `aLAT` are cartesian closed when the explicit algebraic
cartesian-closed data is supplied. -/
theorem cor_4_1_6_algebraic_lattice_like_categories_cartesian_closed_of_data
    (hData : AlgebraicLatticeLikeCartesianClosedData.{u}) :
    DomainClass.CartesianClosed (AlgebraicLDomainClass : DomainClass.{u}) ∧
      DomainClass.CartesianClosed (AlgebraicBcDomainClass : DomainClass.{u}) ∧
        DomainClass.CartesianClosed
          (AlgebraicContinuousLatticeDomainClass : DomainClass.{u}) := by
  exact hData.cartesian_closed

/-- Corollary 4.1.6, algebraic counterpart clause.  The source proof for the
algebraic closure package is not formalized here, so the direct statement is
registered as local proof debt. -/
theorem cor_4_1_6_algebraic_lattice_like_categories_cartesian_closed :
    DomainClass.CartesianClosed (AlgebraicLDomainClass : DomainClass.{u}) ∧
      DomainClass.CartesianClosed (AlgebraicBcDomainClass : DomainClass.{u}) ∧
        DomainClass.CartesianClosed
          (AlgebraicContinuousLatticeDomainClass : DomainClass.{u}) := by
  admit

/-- Corollary 4.1.6, PDF text: "The categories L, BC, LAT, and their algebraic
counterparts are cartesian closed." Auxiliary combined data form: L, BC, LAT and the
algebraic counterparts `aL`, `aBC`, and `aLAT` satisfy the local
cartesian-closed closure property when the continuous function-space data
and the algebraic counterpart data are supplied. -/
theorem cor_4_1_6_lattice_like_and_algebraic_categories_cartesian_closed_of_data
    (hFunctionSpaces : LatticeLikeFunctionSpaceData.{u})
    (hAlgebraic : AlgebraicLatticeLikeCartesianClosedData.{u}) :
    DomainClass.CartesianClosed (LDomainClass : DomainClass.{u}) ∧
      DomainClass.CartesianClosed (BcDomainClass : DomainClass.{u}) ∧
        DomainClass.CartesianClosed (ContinuousLatticeDomainClass : DomainClass.{u}) ∧
          DomainClass.CartesianClosed (AlgebraicLDomainClass : DomainClass.{u}) ∧
            DomainClass.CartesianClosed (AlgebraicBcDomainClass : DomainClass.{u}) ∧
              DomainClass.CartesianClosed
                (AlgebraicContinuousLatticeDomainClass : DomainClass.{u}) := by
  rcases cor_4_1_6_lattice_like_categories_cartesian_closed_of_functionSpaceData hFunctionSpaces with
    ⟨hL, hBC, hLAT⟩
  rcases cor_4_1_6_algebraic_lattice_like_categories_cartesian_closed_of_data hAlgebraic with
    ⟨haL, haBC, haLAT⟩
  exact ⟨hL, hBC, hLAT, haL, haBC, haLAT⟩

/-- Corollary 4.1.6, PDF text: "The categories L, BC, LAT, and their algebraic
counterparts are cartesian closed."  Direct registered placeholder for the
combined statement, without treating the auxiliary principle packages as the
proof of the numbered result. -/
theorem cor_4_1_6_lattice_like_and_algebraic_categories_cartesian_closed :
    DomainClass.CartesianClosed (LDomainClass : DomainClass.{u}) ∧
      DomainClass.CartesianClosed (BcDomainClass : DomainClass.{u}) ∧
        DomainClass.CartesianClosed (ContinuousLatticeDomainClass : DomainClass.{u}) ∧
          DomainClass.CartesianClosed (AlgebraicLDomainClass : DomainClass.{u}) ∧
            DomainClass.CartesianClosed (AlgebraicBcDomainClass : DomainClass.{u}) ∧
              DomainClass.CartesianClosed
                (AlgebraicContinuousLatticeDomainClass : DomainClass.{u}) := by
  rcases cor_4_1_6_lattice_like_categories_cartesian_closed with
    ⟨hL, hBC, hLAT⟩
  rcases cor_4_1_6_algebraic_lattice_like_categories_cartesian_closed with
    ⟨haL, haBC, haLAT⟩
  exact ⟨hL, hBC, hLAT, haL, haBC, haLAT⟩

end Chapter4
end AbramskyJung

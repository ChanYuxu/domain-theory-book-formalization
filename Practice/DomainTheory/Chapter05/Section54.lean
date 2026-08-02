import Practice.DomainTheory.Chapter05.Section53

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 5.4

Admissible relations and the induction/coinduction principles for canonical
solutions.

The relation-action definition contains only the data and compatibility laws
from Definition 5.4.3.  Fixed-point consequences remain separate theorems.
-/

universe u v

namespace AbramskyJung
namespace Chapter5

open Chapter4

/-- Pointwise image of an indexed relation under a continuous map. -/
def relationImage
    {ι : Type v} {D E : OrderedDomain.{u}}
    (f : OrderedDomain.ContFunCarrier D E)
    (R : Set (ι → D.carrier)) : Set (ι → E.carrier) :=
  {ys | ∃ xs ∈ R, ys = fun i : ι => f (xs i)}

/-- Pointwise order relation as a binary relation encoded by `Bool`-indexed tuples. -/
def orderTupleRelation (D : OrderedDomain.{u}) : Set (Bool → D.carrier) :=
  {p | p false ≤ p true}

/-- The whole indexed tuple relation. -/
def wholeTupleRelation {ι : Type v} (D : OrderedDomain.{u}) : Set (ι → D.carrier) :=
  Set.univ

/-- The unary whole relation, encoded by `Unit`-indexed tuples. -/
abbrev unaryWholeRelation (D : OrderedDomain.{u}) : Set (Unit → D.carrier) :=
  wholeTupleRelation D

/-- Definition 5.4.1: admissible n-ary relations on a pointed domain.
PDF source: `R ⊆ D^n` contains the constantly-bottom tuple and is closed under
suprema of omega-chains; unary instances are admissible predicates. -/
structure def_5_4_1_admissible_relations
    (D : OrderedDomain.{u}) (ι : Type v) [OrderBot D.carrier]
    (R : Set (ι → D.carrier)) : Prop where
  contains_bottom : (fun _ : ι => ⊥) ∈ R
  closed_omega_chains :
    ∀ (c : Nat → ι → D.carrier) (s : ι → D.carrier),
      (∀ n : Nat, c n ∈ R) →
        (∀ n : Nat, ∀ i : ι, c n i ≤ c (n + 1) i) →
        (∀ i : ι, Chapter3.IsSup (Set.range fun n : Nat => c n i) (s i)) →
          s ∈ R

private theorem unaryWholeRelation_admissible
    (D : OrderedDomain.{u}) [OrderBot D.carrier] :
    def_5_4_1_admissible_relations D Unit (unaryWholeRelation D) := by
  constructor
  · simp [unaryWholeRelation, wholeTupleRelation]
  · intro _ _ _ _ _
    simp [unaryWholeRelation, wholeTupleRelation]

private theorem orderTupleRelation_admissible
    (D : OrderedDomain.{u}) [OrderBot D.carrier] :
    def_5_4_1_admissible_relations D Bool (orderTupleRelation D) := by
  constructor
  · simp [orderTupleRelation]
  · intro c s hc _hmono hs
    have hUpper :
        Chapter3.IsUpperBound (Set.range fun n : Nat => c n false) (s true) := by
      intro a ha
      rcases ha with ⟨n, rfl⟩
      exact le_trans (by simpa [orderTupleRelation] using hc n)
        ((hs true).1 ⟨n, rfl⟩)
    exact (hs false).2 (s true) hUpper

/-- Strict continuous maps between pointed ordered domains, reusing the
Chapter 3 strict function-space carrier. -/
abbrev StrictContinuousMap (D E : OrderedDomain.{u}) : Type u :=
  Chapter3.StrictContFun D.carrier E.carrier

namespace StrictContinuousMap

/-- Forget a strict continuous map to an ordinary continuous map. -/
def map {D E : OrderedDomain.{u}} (f : StrictContinuousMap D E) :
    OrderedDomain.ContFunCarrier D E where
  toFun := f.toFun
  continuous := f.continuous

/-- Identity strict continuous map. -/
def id (D : OrderedDomain.{u}) : StrictContinuousMap D D where
  toFun := fun x => x
  continuous := Chapter3.scottContinuous_id
  strict := fun _ hx => hx

end StrictContinuousMap

/-- The strict continuous function-space object, ordered pointwise through the
underlying continuous maps. -/
def strictFunctionSpace (D E : OrderedDomain.{u}) :
    OrderedDomain.{u} where
  carrier := StrictContinuousMap D E
  preorder := inferInstance

instance strictFunctionSpaceOrderBot
    (D E : OrderedDomain.{u}) [OrderBot E.carrier] :
    OrderBot (strictFunctionSpace D E).carrier where
  bot := Chapter3.StrictContFun.const (D := D.carrier) (E := E.carrier)
    (⊥ : E.carrier) (fun _ => bot_le)
  bot_le _ _ := bot_le

/-- Pointwise bottom for the ordinary continuous function-space object.  This
instance is tied to `OrderedDomain.functionSpace`'s explicit pointwise
preorder. -/
instance continuousFunctionSpaceObjectOrderBot
    (D E : OrderedDomain.{u}) [OrderBot E.carrier] :
    OrderBot (OrderedDomain.functionSpace D E).carrier where
  bot := Chapter3.ContFun.const (D := D.carrier) (E := E.carrier) ⊥
  bot_le _ _ := bot_le

private theorem omegaChain_range_directed
    {α : Type u} [Preorder α] (c : Nat → α)
    (hc : ∀ n : Nat, c n ≤ c (n + 1)) :
    Chapter3.DirectedSet (Set.range c) := by
  have hmono : ∀ ⦃m n : Nat⦄, m ≤ n → c m ≤ c n := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact le_rfl
    | succ n _ ih => exact le_trans ih (hc n)
  constructor
  · exact ⟨c 0, ⟨0, rfl⟩⟩
  · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ⟨c (max m n), ⟨max m n, rfl⟩,
      hmono (Nat.le_max_left m n), hmono (Nat.le_max_right m n)⟩

/-- Predicate on function spaces induced by relational inclusion. -/
def relationTransformerPredicate
    {ι : Type v} (D E : OrderedDomain.{u})
    (R : Set (ι → D.carrier)) (S : Set (ι → E.carrier)) :
    Set (OrderedDomain.ContFunCarrier D E) :=
  {f | relationImage f R ⊆ S}

/-- Predicate on strict function spaces induced by relational inclusion. -/
def strictRelationTransformerPredicate
    {ι : Type v} (D E : OrderedDomain.{u}) [OrderBot D.carrier] [OrderBot E.carrier]
    (R : Set (ι → D.carrier)) (S : Set (ι → E.carrier)) :
    Set (strictFunctionSpace D E).carrier :=
  {f | relationImage f.map R ⊆ S}

/-- Proposition 5.4.2, strict-map form matching the PDF.  PDF text:
`{f | f^rel(R) ⊆ S}` is admissible on the strict function space when `R` and
`S` are admissible.

The proof uses pointwise suprema of strict maps and Scott-continuity of
evaluation from Chapter 3. -/
theorem prop_5_4_2_admissible_relation_closure_strict
    {ι : Type v} (D E : OrderedDomain.{u})
    [OrderBot D.carrier] [OrderBot E.carrier]
    (_hD : Chapter3.IsDcpo D.carrier) (hE : Chapter3.IsDcpo E.carrier)
    {R : Set (ι → D.carrier)} {S : Set (ι → E.carrier)}
    (_hR : def_5_4_1_admissible_relations D ι R)
    (hS : def_5_4_1_admissible_relations E ι S) :
    AdmissiblePredicate (strictFunctionSpace D E)
      (strictRelationTransformerPredicate D E R S) := by
  constructor
  · rintro ys ⟨xs, _hxs, rfl⟩
    convert hS.contains_bottom using 1
  · intro c s hc hmono hs
    change Nat → StrictContinuousMap D E at c
    change StrictContinuousMap D E at s
    rintro ys ⟨xs, hxs, rfl⟩
    apply hS.closed_omega_chains
        (fun n i => (c n) (xs i)) (fun i => s (xs i))
    · intro n
      exact hc n ⟨xs, hxs, rfl⟩
    · intro n i
      exact hmono n (xs i)
    · intro i
      have hdir : Chapter3.DirectedSet (Set.range c) :=
        omegaChain_range_directed c hmono
      have heval :=
        (Chapter3.StrictContFun.eval_scottContinuous hE (xs i)).maps_isSup hdir hs
      have himage :
          (fun f : StrictContinuousMap D E => f (xs i)) '' Set.range c =
            Set.range (fun n : Nat => (c n) (xs i)) := by
        ext y
        constructor
        · rintro ⟨f, ⟨n, rfl⟩, rfl⟩
          exact ⟨n, rfl⟩
        · rintro ⟨n, rfl⟩
          exact ⟨c n, ⟨n, rfl⟩, rfl⟩
      rw [himage] at heval
      exact heval

/-- Proposition 5.4.2, continuous-map convenience form retained for the local
function-space interface. -/
theorem prop_5_4_2_admissible_relation_closure
    {ι : Type v} (D E : OrderedDomain.{u})
    [OrderBot D.carrier] [OrderBot E.carrier]
    (_hD : Chapter3.IsDcpo D.carrier) (hE : Chapter3.IsDcpo E.carrier)
    {R : Set (ι → D.carrier)} {S : Set (ι → E.carrier)}
    (_hR : def_5_4_1_admissible_relations D ι R)
    (hS : def_5_4_1_admissible_relations E ι S) :
    AdmissiblePredicate (OrderedDomain.functionSpace D E)
      (relationTransformerPredicate D E R S) := by
  constructor
  · rintro ys ⟨xs, _hxs, rfl⟩
    convert hS.contains_bottom using 1
  · intro c s hc hmono hs
    change Nat → OrderedDomain.ContFunCarrier D E at c
    change OrderedDomain.ContFunCarrier D E at s
    rintro ys ⟨xs, hxs, rfl⟩
    apply hS.closed_omega_chains
        (fun n i => (c n) (xs i)) (fun i => s (xs i))
    · intro n
      exact hc n ⟨xs, hxs, rfl⟩
    · intro n i
      exact hmono n (xs i)
    · intro i
      have hdir : Chapter3.DirectedSet (Set.range c) :=
        omegaChain_range_directed c hmono
      have heval :=
        (Chapter3.ContFun.eval_scottContinuous hE (xs i)).maps_isSup hdir hs
      have himage :
          (fun f : OrderedDomain.ContFunCarrier D E => f (xs i)) '' Set.range c =
            Set.range (fun n : Nat => (c n) (xs i)) := by
        ext y
        constructor
        · rintro ⟨f, ⟨n, rfl⟩, rfl⟩
          exact ⟨n, rfl⟩
        · rintro ⟨n, rfl⟩
          exact ⟨c n, ⟨n, rfl⟩, rfl⟩
      rw [himage] at heval
      exact heval

/-- Definition 5.4.3: actions of functors on admissible relations.
PDF source: a mixed-variant locally continuous functor maps pairs of admissible
relations to an admissible relation, compatibly with strict morphisms. -/
structure def_5_4_3_relation_action
    (F : MixedVariantFunctor.{u}) (ι : Type v) where
  locally_continuous : def_5_2_5_mixed_variant_locally_continuous F
  rel :
    ∀ D E : OrderedDomain.{u},
      Set (ι → D.carrier) →
        Set (ι → E.carrier) →
          Set (ι → (F.mapObj D E).carrier)
  maps_admissible :
    ∀ (D E : OrderedDomain.{u}) [OrderBot D.carrier] [OrderBot E.carrier]
      [OrderBot (F.mapObj D E).carrier] {R : Set (ι → D.carrier)}
      {S : Set (ι → E.carrier)},
        def_5_4_1_admissible_relations D ι R →
          def_5_4_1_admissible_relations E ι S →
            def_5_4_1_admissible_relations (F.mapObj D E) ι (rel D E R S)
  compatible :
    ∀ {D₁ D₂ E₁ E₂ : OrderedDomain.{u}}
      [OrderBot D₁.carrier] [OrderBot D₂.carrier]
      [OrderBot E₁.carrier] [OrderBot E₂.carrier]
      (f : StrictContinuousMap D₂ D₁) (g : StrictContinuousMap E₁ E₂)
      {R₁ : Set (ι → D₁.carrier)} {R₂ : Set (ι → D₂.carrier)}
      {S₁ : Set (ι → E₁.carrier)} {S₂ : Set (ι → E₂.carrier)},
        relationImage f.map R₂ ⊆ R₁ →
          relationImage g.map S₁ ⊆ S₂ →
            relationImage (F.mapHom f.map g.map) (rel D₁ E₁ R₁ S₁) ⊆
              rel D₂ E₂ R₂ S₂

/-- Antitone/monotone behavior of an admissible relation action. -/
def RelationActionAntitoneMonotone
    {ι : Type v} {F : MixedVariantFunctor.{u}}
    (A : def_5_4_3_relation_action F ι) : Prop :=
  ∀ (D E : OrderedDomain.{u}) [OrderBot D.carrier] [OrderBot E.carrier]
    {R₁ R₂ : Set (ι → D.carrier)} {S₁ S₂ : Set (ι → E.carrier)},
    R₂ ⊆ R₁ → S₁ ⊆ S₂ →
      A.rel D E R₁ S₁ ⊆ A.rel D E R₂ S₂

/-- Proposition 5.4.4: antitone/monotone functoriality of relation actions,
derived by specializing the compatibility law to strict identity maps.
PDF source: the relation-action maps are antitone in the first argument and
monotone in the second. -/
theorem prop_5_4_4_relation_action_functoriality
    {ι : Type v} {F : MixedVariantFunctor.{u}}
    (A : def_5_4_3_relation_action F ι) :
    RelationActionAntitoneMonotone A := by
  intro D E _ _ R₁ R₂ S₁ S₂ hR hS xs hxs
  let fid : StrictContinuousMap D D := StrictContinuousMap.id D
  let gid : StrictContinuousMap E E := StrictContinuousMap.id E
  have hcompat :
      relationImage (F.mapHom fid.map gid.map) (A.rel D E R₁ S₁) ⊆
        A.rel D E R₂ S₂ := by
    exact A.compatible fid gid
      (by
        rintro ys ⟨zs, hzs, rfl⟩
        exact hR hzs)
      (by
        rintro ys ⟨zs, hzs, rfl⟩
        exact hS hzs)
  have hImage :
      (fun i : ι => F.mapHom fid.map gid.map (xs i)) ∈
        relationImage (F.mapHom fid.map gid.map) (A.rel D E R₁ S₁) :=
    ⟨xs, hxs, rfl⟩
  have hMapped :
      (fun i : ι => F.mapHom fid.map gid.map (xs i)) ∈ A.rel D E R₂ S₂ :=
    hcompat hImage
  convert hMapped using 1
  funext i
  exact (F.mapHom_id (D := D) (E := E) (xs i)).symm

/-- Strict-category data used by Theorem 5.4.5.  These fields make explicit
that the mixed functor and the canonical fold/unfold maps live in
`D_{⊥!}`; they contain no relational conclusion. -/
structure StrictMixedCanonicalData
    (F : MixedVariantFunctor.{u}) (C : MixedCanonicalSolution F)
    [OrderBot C.solution.object.carrier]
    [OrderBot (F.mapObj C.solution.object C.solution.object).carrier] : Prop where
  fold_strict : Chapter2.StrictMap C.solution.fold
  unfold_strict : Chapter2.StrictMap C.solution.unfold
  mapHom_diagonal_strict :
    ∀ g : OrderedDomain.ContFunCarrier C.solution.object C.solution.object,
      Chapter2.StrictMap g → Chapter2.StrictMap (F.mapHom g g)

/-- Theorem 5.4.5.  PDF text: for the canonical fixed point, the two
unfold/fold relational inclusions imply `R ⊆ S`.

The proof follows the printed admissible-predicate argument on the continuous
function space and uses Theorem 5.3.7 to identify the Kleene least fixed point
with the identity. -/
theorem theorem_5_4_5_admissible_relation_actions_exist
    {ι : Type v} (F : MixedVariantFunctor.{u})
    (A : def_5_4_3_relation_action F ι)
    (C : MixedCanonicalSolution F)
    [OrderBot C.solution.object.carrier]
    [OrderBot (F.mapObj C.solution.object C.solution.object).carrier]
    (hStrict : StrictMixedCanonicalData F C)
    {R S : Set (ι → C.solution.object.carrier)}
    (hR : def_5_4_1_admissible_relations C.solution.object ι R)
    (hS : def_5_4_1_admissible_relations C.solution.object ι S)
    (hunfold : relationImage C.solution.unfold R ⊆ A.rel C.solution.object C.solution.object S R)
    (hfold : relationImage C.solution.fold (A.rel C.solution.object C.solution.object R S) ⊆ S) :
    R ⊆ S := by
  let D := C.solution.object
  letI homBot : OrderBot (OrderedDomain.ContFunCarrier D D) :=
    { bot := Chapter3.ContFun.const (⊥ : D.carrier)
      bot_le := fun _ _ => bot_le }
  let phi : Chapter3.ContFun
      (OrderedDomain.ContFunCarrier D D) (OrderedDomain.ContFunCarrier D D) :=
    { toFun := mixedEndomorphismFunctional F C.solution
      continuous := by
        have hDiagonal : Chapter3.ScottContinuous
            (fun g : OrderedDomain.ContFunCarrier D D => (g, g)) :=
          Chapter3.prod_pair_scottContinuous Chapter3.scottContinuous_id
            Chapter3.scottContinuous_id
        have hMap : Chapter3.ScottContinuous
            (fun g : OrderedDomain.ContFunCarrier D D => F.mapHom g g) :=
          Chapter3.ScottContinuous.comp
            (A.locally_continuous.hom_continuous
              (D₁ := D) (D₂ := D) (E₁ := D) (E₂ := D)) hDiagonal
        change Chapter3.ScottContinuous
          (fun g : OrderedDomain.ContFunCarrier D D =>
            OrderedDomain.compContFun C.solution.fold
              (OrderedDomain.compContFun (F.mapHom g g) C.solution.unfold))
        exact Chapter3.ScottContinuous.comp
          (f := fun q : OrderedDomain.ContFunCarrier (F.mapObj D D) (F.mapObj D D) =>
            OrderedDomain.compContFun C.solution.fold
              (OrderedDomain.compContFun q C.solution.unfold))
          (g := fun g : OrderedDomain.ContFunCarrier D D => F.mapHom g g)
          (whisker_scottContinuous D (F.mapObj D D) (F.mapObj D D) D
            C.construction.functor_solution_dcpo C.solution.unfold C.solution.fold)
          hMap }
  let P := relationTransformerPredicate D D R S
  have hP : AdmissiblePredicate (OrderedDomain.functionSpace D D) P :=
    prop_5_4_2_admissible_relation_closure D D
      C.construction.solution_dcpo C.construction.solution_dcpo hR hS
  have hPhiStrict : ∀ g : OrderedDomain.ContFunCarrier D D,
      Chapter2.StrictMap g → Chapter2.StrictMap (phi g) := by
    intro g hg
    change C.solution.fold (F.mapHom g g (C.solution.unfold ⊥)) = ⊥
    rw [hStrict.unfold_strict]
    rw [hStrict.mapHom_diagonal_strict g hg]
    exact hStrict.fold_strict
  have hPhiPreservesP : ∀ g : OrderedDomain.ContFunCarrier D D,
      Chapter2.StrictMap g → g ∈ P → phi g ∈ P := by
    intro g hgStrict hgP
    let sg : StrictContinuousMap D D :=
      { toFun := g
        continuous := g.continuous
        strict := by
          intro x hx y
          calc
            g x ≤ g ⊥ := g.continuous.1 (hx ⊥)
            _ = ⊥ := hgStrict
            _ ≤ y := bot_le }
    have hMapped : relationImage (F.mapHom sg.map sg.map)
        (A.rel D D S R) ⊆ A.rel D D R S := by
      exact A.compatible sg sg hgP hgP
    rintro ys ⟨xs, hxs, rfl⟩
    have hUnfolded : (fun i => C.solution.unfold (xs i)) ∈ A.rel D D S R :=
      hunfold ⟨xs, hxs, rfl⟩
    have hFunctorMapped :
        (fun i => F.mapHom g g (C.solution.unfold (xs i))) ∈ A.rel D D R S := by
      exact hMapped ⟨(fun i => C.solution.unfold (xs i)), hUnfolded, rfl⟩
    exact hfold ⟨(fun i => F.mapHom g g (C.solution.unfold (xs i))),
      hFunctorMapped, rfl⟩
  let l := preorderChosenLeastFix
    (Chapter3.ContFun.isDcpo_of_codomain C.construction.solution_dcpo) phi
  let iter : Nat → OrderedDomain.ContFunCarrier D D :=
    preorderBotIter (fun g : OrderedDomain.ContFunCarrier D D => phi g)
  have hIter : ∀ n : Nat,
      iter n ∈ P ∧ Chapter2.StrictMap (iter n) := by
    intro n
    induction n with
    | zero =>
        exact ⟨hP.contains_bottom, rfl⟩
    | succ n ih =>
        exact ⟨hPhiPreservesP _ ih.2 ih.1, hPhiStrict _ ih.2⟩
  have hIterMono : ∀ n : Nat,
      iter n ≤ iter (n + 1) := by
    intro n
    induction n with
    | zero => exact bot_le
    | succ n ih => exact phi.continuous.1 ih
  have hRangeDirected : Chapter3.DirectedSet (preorderIterSet phi) :=
    by simpa [preorderIterSet, iter] using omegaChain_range_directed iter hIterMono
  have hSup : Chapter3.IsSup (preorderIterSet phi) l :=
    Classical.choose_spec
      ((Chapter3.ContFun.isDcpo_of_codomain C.construction.solution_dcpo)
        (preorderIterSet phi) hRangeDirected)
  have hLInP : l ∈ P := by
    apply hP.closed_omega_chains iter l
    · exact fun n => (hIter n).1
    · intro n x
      exact hIterMono n x
    · simpa [preorderIterSet, iter] using hSup
  have hMapAnti : ∀ f g : OrderedDomain.ContFunCarrier D D,
      f ≤ g → g ≤ f → f = g := by
    intro f g hfg hgf
    apply Chapter3.ContFun.ext_apply
    intro x
    exact C.construction.solution_antisymm _ _ (hfg x) (hgf x)
  have hSpec := preorderChosenLeastFix_spec
    (Chapter3.ContFun.isDcpo_of_codomain C.construction.solution_dcpo)
      hMapAnti phi
  have hIdentity : IdentityIsLeastMixedFunctionalFixpoint F C.solution :=
    (identityLeastMixedEndomorphism_iff_identityLeastMixedFunctionalFixpoint
      F C.solution).1 (canonicalIdentityIsLeastMixedEndomorphism F C)
  have hLEqIdentity : l = OrderedDomain.idContFun D := by
    apply hMapAnti
    · exact hSpec.2 (OrderedDomain.idContFun D) hIdentity.1
    · exact hIdentity.2 l hSpec.1
  have hIdentityInP : OrderedDomain.idContFun D ∈ P := by
    rw [← hLEqIdentity]
    exact hLInP
  change relationImage (OrderedDomain.idContFun D) R ⊆ S at hIdentityInP
  intro xs hxs
  have hx := hIdentityInP ⟨xs, hxs, rfl⟩
  simpa using hx

/-- Definition 5.4.6: logical admissible actions.
PDF source: an action is logical when `F^rel(R, E^n) = F(D,E)^n` for
admissible `R`. -/
def def_5_4_6_logical_admissible_action
    {ι : Type v}
    {F : MixedVariantFunctor.{u}}
    (A : def_5_4_3_relation_action F ι) : Prop :=
  ∀ (D E : OrderedDomain.{u}) [OrderBot D.carrier] [OrderBot E.carrier]
    (R : Set (ι → D.carrier)),
    def_5_4_1_admissible_relations D ι R →
    A.rel D E R (wholeTupleRelation E) =
      wholeTupleRelation (F.mapObj D E)

/-- Theorem 5.4.7: induction for canonical fixed points, derived from the
current relation-action inclusion interface.
PDF source: an admissible predicate closed under `fold` for a logical action is
the whole canonical fixed point. -/
theorem theorem_5_4_7_induction
    (F : MixedVariantFunctor.{u})
    (A : def_5_4_3_relation_action F Unit)
    (hA : def_5_4_6_logical_admissible_action A)
    (C : MixedCanonicalSolution F)
    [OrderBot C.solution.object.carrier]
    [OrderBot (F.mapObj C.solution.object C.solution.object).carrier]
    (hStrict : StrictMixedCanonicalData F C)
    {S : Set (Unit → C.solution.object.carrier)}
    (hS : def_5_4_1_admissible_relations C.solution.object Unit S)
    (hfold :
      relationImage C.solution.fold
        (A.rel C.solution.object C.solution.object (wholeTupleRelation C.solution.object) S) ⊆ S) :
    S = wholeTupleRelation C.solution.object := by
  apply Set.Subset.antisymm
  · intro x _
    simp [wholeTupleRelation]
  · exact theorem_5_4_5_admissible_relation_actions_exist F A C hStrict
      (unaryWholeRelation_admissible C.solution.object) hS
      (by
        intro xs _
        rw [hA C.solution.object C.solution.object S hS]
        simp [wholeTupleRelation])
      hfold

/-- Definition 5.4.8: extensional admissible actions.
PDF source: an action is extensional when `F^rel(R, ⊑E) = ⊑F(D,E)` for
admissible binary `R`. -/
def def_5_4_8_extensional_admissible_action
    {F : MixedVariantFunctor.{u}}
    (A : def_5_4_3_relation_action F Bool) : Prop :=
  ∀ (D E : OrderedDomain.{u}) [OrderBot D.carrier] [OrderBot E.carrier]
    (R : Set (Bool → D.carrier)),
    def_5_4_1_admissible_relations D Bool R →
    A.rel D E R (orderTupleRelation E) =
      orderTupleRelation (F.mapObj D E)

/-- Simulations for the canonical mixed fixed point. -/
def IsSimulation
    {F : MixedVariantFunctor.{u}}
    (A : def_5_4_3_relation_action F Bool)
    (C : MixedCanonicalSolution F)
    [OrderBot C.solution.object.carrier]
    [OrderBot (F.mapObj C.solution.object C.solution.object).carrier]
    (R : Set (Bool → C.solution.object.carrier)) : Prop :=
  def_5_4_1_admissible_relations C.solution.object Bool R ∧
    relationImage C.solution.unfold R ⊆
      A.rel C.solution.object C.solution.object (orderTupleRelation C.solution.object) R

/-- Theorem 5.4.9: coinduction for canonical fixed points, derived from the
current relation-action inclusion interface.
PDF source: an admissible simulation whose unfold image lies in `F^rel(⊑D, R)`
is contained in the canonical order. -/
theorem theorem_5_4_9_coinduction
    (F : MixedVariantFunctor.{u})
    (A : def_5_4_3_relation_action F Bool)
    (hA : def_5_4_8_extensional_admissible_action A)
    (C : MixedCanonicalSolution F)
    [OrderBot C.solution.object.carrier]
    [OrderBot (F.mapObj C.solution.object C.solution.object).carrier]
    (hStrict : StrictMixedCanonicalData F C)
    {R : Set (Bool → C.solution.object.carrier)}
    (hR : IsSimulation A C R) :
    R ⊆ orderTupleRelation C.solution.object := by
  refine theorem_5_4_5_admissible_relation_actions_exist F A C hStrict hR.1
    (orderTupleRelation_admissible C.solution.object) hR.2 ?_
  intro ys hys
  rcases hys with ⟨xs, hxs, rfl⟩
  rw [hA C.solution.object C.solution.object R hR.1] at hxs
  exact Chapter3.ScottContinuous.monotone C.solution.fold.continuous hxs

/-- Corollary 5.4.10: order is characterized by simulation.
PDF source: two canonical fixed-point elements are ordered exactly when related
by a simulation. -/
theorem cor_5_4_10_order_iff_simulation
    (F : MixedVariantFunctor.{u})
    (A : def_5_4_3_relation_action F Bool)
    (hA : def_5_4_8_extensional_admissible_action A)
    (C : MixedCanonicalSolution F)
    [OrderBot C.solution.object.carrier]
    [OrderBot (F.mapObj C.solution.object C.solution.object).carrier]
    (hStrict : StrictMixedCanonicalData F C)
    (x y : C.solution.object.carrier) :
    x ≤ y ↔
      ∃ R : Set (Bool → C.solution.object.carrier),
        IsSimulation A C R ∧ (fun b : Bool => if b then y else x) ∈ R := by
  constructor
  · intro hxy
    refine ⟨orderTupleRelation C.solution.object, ?_, ?_⟩
    · constructor
      · exact orderTupleRelation_admissible C.solution.object
      · intro ys hys
        rcases hys with ⟨xs, hxs, rfl⟩
        rw [hA C.solution.object C.solution.object (orderTupleRelation C.solution.object)
          (orderTupleRelation_admissible C.solution.object)]
        exact Chapter3.ScottContinuous.monotone C.solution.unfold.continuous hxs
    · simpa [orderTupleRelation] using hxy
  · rintro ⟨R, hR, hxy⟩
    have hsub := theorem_5_4_9_coinduction F A hA C hStrict hR
    exact hsub hxy

end Chapter5
end AbramskyJung

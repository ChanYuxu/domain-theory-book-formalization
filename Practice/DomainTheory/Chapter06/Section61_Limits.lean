import Practice.DomainTheory.Chapter06.Core

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Chapter 6.1 support: limits of dcpo algebras

This module constructs arbitrary products and equalizers of dcpo algebras.  It
contains the complete proof of Proposition 6.1.1 and is kept separate from the
free-algebra constructions in `Section61.lean` because the limit proof is a
self-contained categorical component.
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

/-- Identity homomorphism of a dcpo algebra. -/
def id {Sig : Signature.{u, v}} {Var : Type w} {T : Theory Sig Var}
    (A : Model T) : DcpoAlgebraHom A A where
  toFun := fun x => x
  continuous := Chapter3.scottContinuous_id
  preserves_op := by
    intro o args
    rfl

/-- Composition of dcpo-algebra homomorphisms. -/
def comp {Sig : Signature.{u, v}} {Var : Type w} {T : Theory Sig Var}
    {A B C : Model T} (g : DcpoAlgebraHom B C) (f : DcpoAlgebraHom A B) :
    DcpoAlgebraHom A C where
  toFun := fun x => g.toFun (f.toFun x)
  continuous := g.continuous.comp f.continuous
  preserves_op := by
    intro o args
    rw [f.preserves_op, g.preserves_op]

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

/-- The arbitrary-product and equalizer criterion used in the textbook's
completeness proof for dcpo algebras.

Both constructions below carry their full concrete universal properties. This
record is nevertheless not itself a `CategoryTheory.HasLimits` instance and
does not encode the standard derivation of all small limits from products and
equalizers. -/
structure CompleteDcpoAlgebraCategory {Sig : Signature.{u, v}} {Var : Type w}
    (T : Theory Sig Var) where
  products : ∀ I : Type w, (A : I → Model T) → Nonempty (DcpoAlgebraProduct I A)
  equalizers :
    ∀ (A B : Model T), (f g : DcpoAlgebraHom A B) →
      Nonempty (DcpoAlgebraEqualizer f g)

/-- The one-point model, kept as a small model-existence sanity witness. -/
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
  antisymm := by
    intro x y _hxy _hyx
    cases x
    cases y
    rfl
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

section PiOrder

variable {I : Type u} {β : I → Type v} [∀ i, Preorder (β i)]

theorem pi_isSup_of_coordinate_isSup
    {S : Set (∀ i, β i)} {s : ∀ i, β i}
    (hs : ∀ i, Chapter3.IsSup ((fun f : ∀ i, β i => f i) '' S) (s i)) :
    Chapter3.IsSup S s := by
  constructor
  · intro f hf i
    exact (hs i).1 ⟨f, hf, rfl⟩
  · intro g hg i
    exact (hs i).2 (g i) (by
      intro x hx
      rcases hx with ⟨f, hf, rfl⟩
      exact hg hf i)

theorem pi_coordinate_isSup
    {S : Set (∀ i, β i)} {s : ∀ i, β i}
    (hs : Chapter3.IsSup S s) (i : I) :
    Chapter3.IsSup ((fun f : ∀ i, β i => f i) '' S) (s i) := by
  constructor
  · intro x hx
    rcases hx with ⟨f, hf, rfl⟩
    exact hs.1 hf i
  · intro y hy
    classical
    let g : ∀ j, β j := Function.update s i y
    have hg : Chapter3.IsUpperBound S g := by
      intro f hf j
      by_cases hji : j = i
      · subst j
        simpa [g] using hy ⟨f, hf, rfl⟩
      · simpa [g, Function.update, hji] using hs.1 hf j
    have hsg : s ≤ g := hs.2 g hg
    simpa [g] using hsg i

theorem pi_eval_scottContinuous (i : I) :
    Chapter3.ScottContinuous (fun f : ∀ i, β i => f i) := by
  constructor
  · intro f g hfg
    exact hfg i
  · intro S s _hS hs
    exact pi_coordinate_isSup hs i

theorem pi_lift_scottContinuous
    {α : Type w} [Preorder α] {f : ∀ i, α → β i}
    (hf : ∀ i, Chapter3.ScottContinuous (f i)) :
    Chapter3.ScottContinuous (fun x i => f i x) := by
  constructor
  · intro x y hxy i
    exact (hf i).1 hxy
  · intro S s hS hs
    apply pi_isSup_of_coordinate_isSup
    intro i
    have hi := (hf i).2 hS hs
    simpa only [Set.image_image] using hi

end PiOrder

namespace DcpoAlgebraHom

theorem ext_apply
    {Sig : Signature.{u, v}} {Var : Type w} {T : Theory Sig Var}
    {A B : Model T} {f g : DcpoAlgebraHom A B}
    (h : ∀ x : A.domain.carrier, f.toFun x = g.toFun x) : f = g := by
  cases f with
  | mk f hf hop =>
      cases g with
      | mk g hg gop =>
          have hfun : f = g := funext h
          subst hfun
          congr

end DcpoAlgebraHom

section Products

variable {Sig : Signature.{u, v}} {Var : Type w} {T : Theory Sig Var}
variable {I : Type w} (A : I → Model T)

noncomputable def dcpoAlgebraProductObject : Model T := by
  classical
  let D : OrderedDomain.{w} := {
    carrier := ∀ i, (A i).domain.carrier
    preorder := inferInstance
  }
  let alg : Algebra Sig D := {
    op := fun o args i => (A i).algebra.op o (fun j => args j i)
  }
  refine {
    domain := D
    dcpo := ?_
    antisymm := ?_
    algebra := alg
    operations_scott_continuous := ?_
    sound := ?_
  }
  · intro S hS
    have hcoordDir : ∀ i, Chapter3.DirectedSet ((fun f : D.carrier => f i) '' S) := by
      intro i
      exact Chapter3.DirectedSet.image
        (f := fun f : D.carrier => f i) (fun _ _ hxy => hxy i) hS
    let s : D.carrier := fun i =>
      Classical.choose ((A i).dcpo _ (hcoordDir i))
    refine ⟨s, pi_isSup_of_coordinate_isSup ?_⟩
    intro i
    exact Classical.choose_spec ((A i).dcpo _ (hcoordDir i))
  · intro f g hfg hgf
    funext i
    exact (A i).antisymm (f i) (g i) (hfg i) (hgf i)
  · intro o
    apply pi_lift_scottContinuous
    intro i
    apply Chapter3.ScottContinuous.comp ((A i).operations_scott_continuous o)
    apply pi_lift_scottContinuous
    intro j
    exact Chapter3.ScottContinuous.comp
      (pi_eval_scottContinuous (β := fun i => (A i).domain.carrier) i)
      (pi_eval_scottContinuous (β := fun _ : Sig.arity o => D.carrier) j)
  · intro e he ρ i
    have eval_coord :
        ∀ t : Term Sig Var,
          Term.eval alg ρ t i =
            Term.eval (A i).algebra (fun x => ρ x i) t := by
      intro t
      induction t with
      | var x => rfl
      | op o args ih =>
          change (A i).algebra.op o (fun j => Term.eval alg ρ (args j) i) = _
          congr
          funext j
          exact ih j
    simpa [eval_coord e.lhs, eval_coord e.rhs] using
      (A i).sound e he (fun x => ρ x i)

def dcpoAlgebraProductProjection (i : I) :
    DcpoAlgebraHom (dcpoAlgebraProductObject A) (A i) where
  toFun := fun f => f i
  continuous := pi_eval_scottContinuous i
  preserves_op := by
    intro o args
    rfl

def dcpoAlgebraProductLift (B : Model T)
    (cone : ∀ i : I, DcpoAlgebraHom B (A i)) :
    DcpoAlgebraHom B (dcpoAlgebraProductObject A) where
  toFun := fun x i => (cone i).toFun x
  continuous := pi_lift_scottContinuous (fun i => (cone i).continuous)
  preserves_op := by
    intro o args
    funext i
    exact (cone i).preserves_op o args

noncomputable def dcpoAlgebraProduct : DcpoAlgebraProduct I A where
  object := dcpoAlgebraProductObject A
  projection := dcpoAlgebraProductProjection A
  lift := dcpoAlgebraProductLift A
  lift_projection := by
    intro B cone i x
    rfl
  lift_unique := by
    intro B cone h hh
    apply DcpoAlgebraHom.ext_apply
    intro x
    funext i
    exact hh i x

end Products

section SubtypeContinuity

variable {α : Type u} {β : Type v} [Preorder α] [Preorder β]
variable {p : β → Prop} {f : α → β}

theorem subtype_mk_scottContinuous
    (hf : Chapter3.ScottContinuous f) (hp : ∀ x, p (f x)) :
    Chapter3.ScottContinuous (fun x => (⟨f x, hp x⟩ : Subtype p)) := by
  constructor
  · intro x y hxy
    exact hf.1 hxy
  · intro S s hS hs
    have hfs : Chapter3.IsSup (f '' S) (f s) := hf.2 hS hs
    constructor
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact hfs.1 ⟨x, hx, rfl⟩
    · intro y hy
      exact hfs.2 y.1 (by
        intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        exact hy ⟨x, hx, rfl⟩)

end SubtypeContinuity

section Equalizers

variable {Sig : Signature.{u, v}} {Var : Type w} {T : Theory Sig Var}
variable {A B : Model T} (f g : DcpoAlgebraHom A B)

abbrev DcpoAlgebraEqualizerCarrier :=
  {x : A.domain.carrier // f.toFun x = g.toFun x}

theorem equalizer_image_eq
    (S : Set (DcpoAlgebraEqualizerCarrier f g)) :
    f.toFun '' (Subtype.val '' S) = g.toFun '' (Subtype.val '' S) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z.1, ⟨z, hz, rfl⟩, z.2.symm⟩
  · intro hy
    rcases hy with ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z.1, ⟨z, hz, rfl⟩, z.2⟩

theorem equalizer_ambient_isSup_of_subtype_isSup
    {S : Set (DcpoAlgebraEqualizerCarrier f g)}
    {s : DcpoAlgebraEqualizerCarrier f g}
    (hS : Chapter3.DirectedSet S) (hs : Chapter3.IsSup S s) :
    Chapter3.IsSup (Subtype.val '' S) s.1 := by
  have hvalDir : Chapter3.DirectedSet (Subtype.val '' S) :=
    Chapter3.DirectedSet.image (fun _ _ hxy => hxy) hS
  rcases A.dcpo (Subtype.val '' S) hvalDir with ⟨t, ht⟩
  have hft : Chapter3.IsSup (f.toFun '' (Subtype.val '' S)) (f.toFun t) :=
    f.continuous.2 hvalDir ht
  have hgt : Chapter3.IsSup (g.toFun '' (Subtype.val '' S)) (g.toFun t) :=
    g.continuous.2 hvalDir ht
  have himage := equalizer_image_eq f g S
  have hft' : Chapter3.IsSup (g.toFun '' (Subtype.val '' S)) (f.toFun t) := by
    simpa only [himage] using hft
  have htEq : f.toFun t = g.toFun t :=
    B.antisymm _ _ (hft'.2 _ hgt.1) (hgt.2 _ hft'.1)
  let t' : DcpoAlgebraEqualizerCarrier f g := ⟨t, htEq⟩
  constructor
  · intro x hx
    rcases hx with ⟨z, hz, rfl⟩
    exact hs.1 hz
  · intro y hy
    have hst : s ≤ t' := hs.2 t' (by
      intro z hz
      exact ht.1 ⟨z, hz, rfl⟩)
    exact le_trans hst (ht.2 y hy)

theorem equalizer_val_scottContinuous :
    Chapter3.ScottContinuous
      (fun x : DcpoAlgebraEqualizerCarrier f g => x.1) := by
  constructor
  · intro x y hxy
    exact hxy
  · intro S s hS hs
    exact equalizer_ambient_isSup_of_subtype_isSup f g hS hs

noncomputable def dcpoAlgebraEqualizerObject : Model T := by
  classical
  let D : OrderedDomain.{w} := {
    carrier := DcpoAlgebraEqualizerCarrier f g
    preorder := inferInstance
  }
  have op_closed :
      ∀ (o : Sig.Op) (args : Sig.arity o → D.carrier),
        f.toFun (A.algebra.op o (fun i => (args i).1)) =
          g.toFun (A.algebra.op o (fun i => (args i).1)) := by
    intro o args
    rw [f.preserves_op, g.preserves_op]
    congr 1
    funext i
    exact (args i).2
  let alg : Algebra Sig D := {
    op := fun o args => ⟨A.algebra.op o (fun i => (args i).1), op_closed o args⟩
  }
  refine {
    domain := D
    dcpo := ?_
    antisymm := ?_
    algebra := alg
    operations_scott_continuous := ?_
    sound := ?_
  }
  · intro S hS
    have hvalDir : Chapter3.DirectedSet (Subtype.val '' S) :=
      Chapter3.DirectedSet.image (fun _ _ hxy => hxy) hS
    rcases A.dcpo (Subtype.val '' S) hvalDir with ⟨s, hs⟩
    have hfs : Chapter3.IsSup (f.toFun '' (Subtype.val '' S)) (f.toFun s) :=
      f.continuous.2 hvalDir hs
    have hgs : Chapter3.IsSup (g.toFun '' (Subtype.val '' S)) (g.toFun s) :=
      g.continuous.2 hvalDir hs
    have himage := equalizer_image_eq f g S
    have hfs' : Chapter3.IsSup (g.toFun '' (Subtype.val '' S)) (f.toFun s) := by
      simpa only [himage] using hfs
    have hsEq : f.toFun s = g.toFun s :=
      B.antisymm _ _ (hfs'.2 _ hgs.1) (hgs.2 _ hfs'.1)
    refine ⟨⟨s, hsEq⟩, ?_⟩
    constructor
    · intro x hx
      exact hs.1 ⟨x, hx, rfl⟩
    · intro y hy
      exact hs.2 y.1 (by
        intro x hx
        rcases hx with ⟨z, hz, rfl⟩
        exact hy hz)
  · intro x y hxy hyx
    apply Subtype.ext
    exact A.antisymm x.1 y.1 hxy hyx
  · intro o
    apply subtype_mk_scottContinuous
    apply Chapter3.ScottContinuous.comp (A.operations_scott_continuous o)
    apply pi_lift_scottContinuous
    intro i
    exact Chapter3.ScottContinuous.comp
      (equalizer_val_scottContinuous f g)
      (pi_eval_scottContinuous
        (β := fun _ : Sig.arity o => DcpoAlgebraEqualizerCarrier f g) i)
  · intro e he ρ
    have eval_val :
        ∀ t : Term Sig Var,
          (Term.eval alg ρ t).1 =
            Term.eval A.algebra (fun x => (ρ x).1) t := by
      intro t
      induction t with
      | var x => rfl
      | op o args ih =>
          change A.algebra.op o (fun j => (Term.eval alg ρ (args j)).1) = _
          congr
          funext j
          exact ih j
    change (Term.eval alg ρ e.lhs).1 ≤ (Term.eval alg ρ e.rhs).1
    simpa only [eval_val e.lhs, eval_val e.rhs] using
      A.sound e he (fun x => (ρ x).1)

def dcpoAlgebraEqualizerInclusion :
    DcpoAlgebraHom (dcpoAlgebraEqualizerObject f g) A where
  toFun := fun x => x.1
  continuous := equalizer_val_scottContinuous f g
  preserves_op := by
    intro o args
    rfl

def dcpoAlgebraEqualizerLift (E : Model T) (h : DcpoAlgebraHom E A)
    (heq : ∀ x : E.domain.carrier, f.toFun (h.toFun x) = g.toFun (h.toFun x)) :
    DcpoAlgebraHom E (dcpoAlgebraEqualizerObject f g) where
  toFun := fun x => ⟨h.toFun x, heq x⟩
  continuous := subtype_mk_scottContinuous h.continuous heq
  preserves_op := by
    intro o args
    apply Subtype.ext
    exact h.preserves_op o args

noncomputable def dcpoAlgebraEqualizer : DcpoAlgebraEqualizer f g where
  object := dcpoAlgebraEqualizerObject f g
  inclusion := dcpoAlgebraEqualizerInclusion f g
  equalizes := fun x => x.2
  lift := dcpoAlgebraEqualizerLift f g
  lift_inclusion := by
    intro E h heq x
    simp [dcpoAlgebraEqualizerInclusion, dcpoAlgebraEqualizerLift]
  lift_unique := by
    intro E h heq k hk
    apply DcpoAlgebraHom.ext_apply
    intro x
    apply Subtype.ext
    simpa [dcpoAlgebraEqualizerInclusion, dcpoAlgebraEqualizerLift] using hk x

end Equalizers

/-- Proposition 6.1.1 proof ingredients. Dcpo algebras of an inequational
theory have arbitrary products and equalizers with explicit universal
properties. The final categorical derivation of all small limits is tracked as
an interface boundary. -/
theorem prop_6_1_1_dcpo_algebras_complete
    {Sig : Signature.{u, v}} {Var : Type w} (T : Theory Sig Var) :
    Nonempty (CompleteDcpoAlgebraCategory T) := by
  classical
  exact ⟨{
    products := fun _I A => ⟨dcpoAlgebraProduct A⟩
    equalizers := fun _A _B f g => ⟨dcpoAlgebraEqualizer f g⟩
  }⟩

end Chapter6
end AbramskyJung

import Practice.DomainTheory.Chapter06

set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-!
# Abramsky--Jung, Domain Theory, Chapter 7

This chapter records the logical presentation of domains: Stone duality,
observables as Scott-open properties, spatial/sober correspondences, and the
logical metalanguage for types, terms, properties, and points.

Audit note: the numbered statements in the split Chapter 7 files are currently
lightweight formal counterparts.  Some are direct definitions or elementary
proofs, while the deeper Stone-duality, sobriety, spectral-duality, and localic
representation results are explicitly marked in their section files as
auxiliary package projections backed by explicit data packages; remaining
weak modeling points are recorded in `formalization_status.md`.
-/

universe u v

namespace AbramskyJung
namespace Chapter7

open Chapter4

/-- A lightweight topological space interface, enough for the duality statements
used in this chapter. -/
structure Space where
  Point : Type u
  IsOpen : Set Point → Prop
  univ_open : IsOpen Set.univ
  inter_open : ∀ U V : Set Point, IsOpen U → IsOpen V → IsOpen (U ∩ V)
  sUnion_open : ∀ S : Set (Set Point), (∀ U ∈ S, IsOpen U) → IsOpen (⋃₀ S)

/-- A frame of observable properties. -/
structure Frame where
  carrier : Type u
  lattice : CompleteLattice carrier

namespace Frame

instance (F : Frame.{u}) : CompleteLattice F.carrier := F.lattice

end Frame

/-- Scott-open observables of an ordered domain. -/
def ScottObservable (D : OrderedDomain.{u}) : Type u :=
  {U : Set D.carrier // Chapter2.ScottOpen U}

/-- A spatial frame comes with enough points to separate frame elements. -/
structure SpatialFrame extends Frame.{u} where
  Point : Type v
  satisfies : Point → carrier → Prop
  separates :
    ∀ a b : carrier,
      (∀ p : Point, satisfies p a ↔ satisfies p b) → a = b

/-- A sober space has enough irreducible closed sets to be represented by points. -/
structure SoberSpace extends Space.{u} where
  genericPointForIrreducibleClosed : Set Point → Option Point

/-- The contravariant maps in the basic Stone adjunction. -/
structure StoneAdjunction where
  opens : Space.{u} → Frame.{u}
  spectrum : Frame.{u} → Space.{u}
  unit : ∀ X : Space.{u}, X.Point → (spectrum (opens X)).Point
  counit : ∀ L : Frame.{u}, (opens (spectrum L)).carrier → L.carrier

/-- A compact-open element of a frame. -/
def CompactOpen (F : Frame.{u}) (a : F.carrier) : Prop :=
  IsCompactElement a

/-- Coherence for a basis of compact-open properties. -/
structure CoherentBasis (F : Frame.{u}) where
  basis : Set F.carrier
  compact : ∀ a ∈ basis, CompactOpen F a
  finite_meet_closed :
    ∀ a ∈ basis, ∀ b ∈ basis, a ⊓ b ∈ basis
  covers : ∀ a : F.carrier, a = sSup {b : F.carrier | b ∈ basis ∧ b ≤ a}

/-- A logical language of types, terms, and observable properties. -/
structure DomainLogic where
  Ty : Type u
  Term : Ty → Type v
  PropOf : Ty → Type v
  denotesType : Ty → OrderedDomain.{v}
  denotesTerm : ∀ T : Ty, Term T → (denotesType T).carrier
  denotesProp : ∀ T : Ty, PropOf T → ScottObservable (denotesType T)

/-- Soundness of a property judgement in the logical metalanguage. -/
def DomainLogic.Valid {L : DomainLogic.{u, v}} {T : L.Ty}
    (t : L.Term T) (p : L.PropOf T) : Prop :=
  L.denotesTerm T t ∈ (L.denotesProp T p).1

end Chapter7
end AbramskyJung

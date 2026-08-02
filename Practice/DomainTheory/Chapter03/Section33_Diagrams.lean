import Practice.DomainTheory.Chapter03.Prelude

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 3.3: diagrams
-/

universe u v w z

namespace AbramskyJung
namespace Chapter3

section Diagrams

/-- Section 3.3.1: a concrete diagram shape using object indices `O` and morphism indices `M`. -/
structure DiagramData (O : Type u) (M : Type v) where
  dom : M → O
  cod : M → O

/-- Cones for a concrete diagram of types and maps. -/
structure Cone
    {O : Type u} {M : Type v} (shape : DiagramData O M)
    (Obj : O → Type w)
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j))
    (C : Type z) where
  leg : ∀ i : O, C → Obj i
  commute : ∀ j : M, ∀ x : C, map j (leg (shape.dom j) x) = leg (shape.cod j) x

/-- Cocones, dual to cones. -/
structure Cocone
    {O : Type u} {M : Type v} (shape : DiagramData O M)
    (Obj : O → Type w)
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j))
    (C : Type z) where
  leg : ∀ i : O, Obj i → C
  commute : ∀ j : M, ∀ x : Obj (shape.dom j), leg (shape.cod j) (map j x) = leg (shape.dom j) x

end Diagrams

end Chapter3
end AbramskyJung

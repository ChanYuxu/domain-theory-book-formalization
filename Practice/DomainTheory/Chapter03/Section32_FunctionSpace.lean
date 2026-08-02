import Practice.DomainTheory.Chapter03.Prelude

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 3.2: function spaces

This file records the carrier-level operations used by the numbered interfaces
in `NumberedItems.lean`.  The continuity proofs for application and the
bundled curry/uncurry order-isomorphism are kept with the numbered Chapter 3
audit declarations, where Lemma 3.2.6 is available.
-/

universe u v w

namespace AbramskyJung
namespace Chapter3

section FunctionSpace

variable {D : Type u} [Preorder D]
variable {E : Type v} [Preorder E]
variable {F : Type w} [Preorder F]

/-- Section 3.2.2: Scott-continuous function space as a bundled type. -/
structure ContFun (D : Type u) (E : Type v) [Preorder D] [Preorder E] where
  toFun : D → E
  continuous : ScottContinuous toFun

namespace ContFun

instance : CoeFun (ContFun D E) (fun _ => D → E) where
  coe f := f.toFun

/-- Pointwise order on continuous maps. -/
def Le (f g : ContFun D E) : Prop := ∀ x : D, f x ≤ g x

/-- Section 3.2.2: continuous maps are ordered pointwise. -/
instance instPreorder : Preorder (ContFun D E) where
  le := Le
  le_refl f x := le_rfl
  le_trans f g h hfg hgh x := le_trans (hfg x) (hgh x)

/-- Section 3.2.2, carrier-level application map. -/
def apply (p : ContFun D E × D) : E := p.1 p.2

/-- Section 3.2.2, raw currying operation on bundled continuous functions.
The result is intentionally unbundled here; continuity is supplied by the
separate-continuity theorem in `NumberedItems.lean`. -/
def curry (f : ContFun (D × E) F) : D → E → F :=
  fun d e => f (d, e)

/-- Section 3.2.2: bundled composition of continuous functions. -/
def comp (g : ContFun E F) (f : ContFun D E) : ContFun D F where
  toFun := fun x => g (f x)
  continuous := g.continuous.comp f.continuous

end ContFun

end FunctionSpace

end Chapter3
end AbramskyJung

import Practice.DomainTheory.Chapter07.Core

set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-!
# Concrete open-set lattices for Chapter 7

This module owns the concrete `Omega(X)` carrier used by both Sections 7.1 and
7.2.  Keeping it below the numbered section modules avoids a backwards import
from the Stone-adjunction proof into its later specializations.
-/

universe u

namespace AbramskyJung
namespace Chapter7

/-- The concrete carrier of the open-set lattice `Omega(X)`. -/
abbrev OpenSet (X : Space.{u}) : Type u :=
  {U : Set X.Point // X.IsOpen U}

namespace OpenSet

instance instPartialOrder (X : Space.{u}) : PartialOrder (OpenSet X) where
  le U V := U.1 ⊆ V.1
  le_refl := by
    intro U x hx
    exact hx
  le_trans := by
    intro U V W hUV hVW x hx
    exact hVW (hUV hx)
  le_antisymm := by
    intro U V hUV hVU
    exact Subtype.ext (Set.Subset.antisymm hUV hVU)

instance instSupSet (X : Space.{u}) : SupSet (OpenSet X) where
  sSup S :=
    ⟨⋃₀ ((fun U : OpenSet X => U.1) '' S), by
      exact X.sUnion_open ((fun U : OpenSet X => U.1) '' S)
        (by
          intro U hU
          rcases hU with ⟨V, _hVS, rfl⟩
          exact V.2)⟩

theorem mem_sSup_iff (X : Space.{u}) (S : Set (OpenSet X)) (x : X.Point) :
    x ∈ (sSup S : OpenSet X).1 ↔ ∃ U ∈ S, x ∈ U.1 := by
  constructor
  · intro hx
    rcases hx with ⟨U, hU, hxU⟩
    rcases hU with ⟨V, hVS, rfl⟩
    exact ⟨V, hVS, hxU⟩
  · intro hx
    rcases hx with ⟨U, hUS, hxU⟩
    exact ⟨U.1, ⟨U, hUS, rfl⟩, hxU⟩

theorem sSup_isLUB (X : Space.{u}) (S : Set (OpenSet X)) :
    IsLUB S (sSup S : OpenSet X) := by
  constructor
  · intro U hUS x hx
    exact (mem_sSup_iff X S x).2 ⟨U, hUS, hx⟩
  · intro U hUpper x hx
    rcases (mem_sSup_iff X S x).1 hx with ⟨V, hVS, hxV⟩
    exact hUpper hVS hxV

@[reducible]
def completeLattice (X : Space.{u}) : CompleteLattice (OpenSet X) :=
  completeLatticeOfSup (OpenSet X) (sSup_isLUB X)

instance instCompleteLattice (X : Space.{u}) : CompleteLattice (OpenSet X) :=
  completeLattice X

theorem top_eq_univ (X : Space.{u}) :
    ((⊤ : OpenSet X).1 : Set X.Point) = Set.univ := by
  apply Set.Subset.antisymm
  · intro x _hx
    exact Set.mem_univ x
  · intro x _hx
    let U : OpenSet X := ⟨Set.univ, X.univ_open⟩
    have hUtop : U ≤ (⊤ : OpenSet X) := le_top
    exact hUtop (Set.mem_univ x)

theorem inf_eq_inter (X : Space.{u}) (U V : OpenSet X) :
    ((U ⊓ V).1 : Set X.Point) = U.1 ∩ V.1 := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨(inf_le_left : U ⊓ V ≤ U) hx, (inf_le_right : U ⊓ V ≤ V) hx⟩
  · intro x hx
    let W : OpenSet X := ⟨U.1 ∩ V.1, X.inter_open U.1 V.1 U.2 V.2⟩
    have hWU : W ≤ U := by
      intro y hy
      exact hy.1
    have hWV : W ≤ V := by
      intro y hy
      exact hy.2
    have hWInf : W ≤ U ⊓ V := le_inf hWU hWV
    exact hWInf hx

end OpenSet

end Chapter7
end AbramskyJung

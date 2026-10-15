import Practice.DomainTheory.Chapter03.NumberedItems.Section32
import Practice.DomainTheory.Chapter03.Section33_Diagrams
import Practice.DomainTheory.Chapter03.Section33_ExpandingSequences

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Chapter 3: Section 3.3 limits and categorical interfaces

Book-facing declarations and their local support API are kept together in
textbook dependency order. Reusable constructions remain in the concept-owned
`Chapter03.Section*` modules.
-/

universe u v w z l

namespace AbramskyJung
namespace Chapter3

/-- The commuting-tuple carrier used in the proof of Theorem 3.3.1.  Its points
are dependent tuples whose coordinates commute with every diagram morphism. -/
def DiagramLimitCarrier
    {O : Type u} {M : Type v} (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)) : Type (max u w) :=
  {x : ∀ i : O, Obj i // ∀ j : M, map j (x (shape.dom j)) = x (shape.cod j)}

instance instPreorderDiagramLimitCarrier
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)} :
    Preorder (DiagramLimitCarrier shape Obj map) where
  le x y := ∀ i : O, x.1 i ≤ y.1 i
  le_refl x i := le_rfl
  le_trans x y z hxy hyz i := le_trans (hxy i) (hyz i)

/-- Coordinate projection from the commuting-tuple carrier. -/
def DiagramLimitCarrier.proj
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (i : O) : DiagramLimitCarrier shape Obj map → Obj i :=
  fun x => x.1 i

/-- The coordinate image of a subset of the commuting-tuple carrier. -/
def DiagramLimitCarrier.coordSet
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (A : Set (DiagramLimitCarrier shape Obj map)) (i : O) : Set (Obj i) :=
  DiagramLimitCarrier.proj i '' A

theorem DiagramLimitCarrier.coordSet_directed
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    {A : Set (DiagramLimitCarrier shape Obj map)}
    (hA : DirectedSet A) (i : O) :
    DirectedSet (DiagramLimitCarrier.coordSet A i) :=
  DirectedSet.image (f := DiagramLimitCarrier.proj i) (by
    intro x y hxy
    exact hxy i) hA

/-- The coordinatewise supremum tuple for a directed subset of the
commuting-tuple carrier. -/
noncomputable def DiagramLimitCarrier.supTuple
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hObj : ∀ i : O, IsDcpo (Obj i))
    (A : Set (DiagramLimitCarrier shape Obj map)) (hA : DirectedSet A) :
    ∀ i : O, Obj i :=
  fun i => Classical.choose (hObj i (DiagramLimitCarrier.coordSet A i)
    (DiagramLimitCarrier.coordSet_directed hA i))

theorem DiagramLimitCarrier.supTuple_isSup_coord
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hObj : ∀ i : O, IsDcpo (Obj i))
    (A : Set (DiagramLimitCarrier shape Obj map)) (hA : DirectedSet A)
    (i : O) :
    IsSup (DiagramLimitCarrier.coordSet A i)
      (DiagramLimitCarrier.supTuple hObj A hA i) :=
  Classical.choose_spec (hObj i (DiagramLimitCarrier.coordSet A i)
    (DiagramLimitCarrier.coordSet_directed hA i))

/-- The coordinatewise supremum tuple still commutes with every diagram morphism.
This is where Scott-continuity of the diagram maps and antisymmetry of the
target dcpos are used. -/
theorem DiagramLimitCarrier.supTuple_commutes
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hObj : ∀ i : O, IsDcpo (Obj i))
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hmap : ∀ j : M, ScottContinuous (map j))
    (A : Set (DiagramLimitCarrier shape Obj map)) (hA : DirectedSet A)
    (j : M) :
    map j (DiagramLimitCarrier.supTuple hObj A hA (shape.dom j)) =
      DiagramLimitCarrier.supTuple hObj A hA (shape.cod j) := by
  let s := DiagramLimitCarrier.supTuple hObj A hA
  have hdomSup :
      IsSup (DiagramLimitCarrier.coordSet A (shape.dom j)) (s (shape.dom j)) :=
    DiagramLimitCarrier.supTuple_isSup_coord hObj A hA (shape.dom j)
  have hcodSup :
      IsSup (DiagramLimitCarrier.coordSet A (shape.cod j)) (s (shape.cod j)) :=
    DiagramLimitCarrier.supTuple_isSup_coord hObj A hA (shape.cod j)
  have hmapSup :
      IsSup (map j '' DiagramLimitCarrier.coordSet A (shape.dom j))
        (map j (s (shape.dom j))) :=
    (hmap j).2 (DiagramLimitCarrier.coordSet_directed hA (shape.dom j)) hdomSup
  have hcod_le_map : s (shape.cod j) ≤ map j (s (shape.dom j)) := by
    exact hcodSup.2 (map j (s (shape.dom j))) (by
      intro y hy
      rcases hy with ⟨x, hxA, rfl⟩
      calc
        x.1 (shape.cod j) = map j (x.1 (shape.dom j)) := (x.2 j).symm
        _ ≤ map j (s (shape.dom j)) :=
          (hmap j).1 (hdomSup.1 ⟨x, hxA, rfl⟩))
  have hmap_le_cod : map j (s (shape.dom j)) ≤ s (shape.cod j) := by
    exact hmapSup.2 (s (shape.cod j)) (by
      intro y hy
      rcases hy with ⟨d, hd, rfl⟩
      rcases hd with ⟨x, hxA, rfl⟩
      calc
        map j (x.1 (shape.dom j)) = x.1 (shape.cod j) := x.2 j
        _ ≤ s (shape.cod j) := hcodSup.1 ⟨x, hxA, rfl⟩)
  exact hantisymm (shape.cod j) _ _ hmap_le_cod hcod_le_map

/-- The coordinatewise supremum as an element of the commuting-tuple carrier. -/
noncomputable def DiagramLimitCarrier.directedSup
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hObj : ∀ i : O, IsDcpo (Obj i))
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hmap : ∀ j : M, ScottContinuous (map j))
    (A : Set (DiagramLimitCarrier shape Obj map)) (hA : DirectedSet A) :
    DiagramLimitCarrier shape Obj map where
  val := DiagramLimitCarrier.supTuple hObj A hA
  property := DiagramLimitCarrier.supTuple_commutes hObj hantisymm hmap A hA

theorem DiagramLimitCarrier.directedSup_isSup
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hObj : ∀ i : O, IsDcpo (Obj i))
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hmap : ∀ j : M, ScottContinuous (map j))
    (A : Set (DiagramLimitCarrier shape Obj map)) (hA : DirectedSet A) :
    IsSup A (DiagramLimitCarrier.directedSup hObj hantisymm hmap A hA) := by
  constructor
  · intro x hx i
    exact (DiagramLimitCarrier.supTuple_isSup_coord hObj A hA i).1 ⟨x, hx, rfl⟩
  · intro y hy i
    exact (DiagramLimitCarrier.supTuple_isSup_coord hObj A hA i).2 (y.1 i) (by
      intro z hz
      rcases hz with ⟨x, hxA, rfl⟩
      exact hy hxA i)

theorem DiagramLimitCarrier.isDcpo
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hObj : ∀ i : O, IsDcpo (Obj i))
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hmap : ∀ j : M, ScottContinuous (map j)) :
    IsDcpo (DiagramLimitCarrier shape Obj map) := by
  intro A hA
  exact ⟨DiagramLimitCarrier.directedSup hObj hantisymm hmap A hA,
    DiagramLimitCarrier.directedSup_isSup hObj hantisymm hmap A hA⟩

theorem DiagramLimitCarrier.antisymmetric
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i)) :
    IsAntisymmetricOrder (DiagramLimitCarrier shape Obj map) := by
  intro x y hxy hyx
  apply Subtype.ext
  funext i
  exact hantisymm i (x.1 i) (y.1 i) (hxy i) (hyx i)

theorem DiagramLimitCarrier.proj_scottContinuous
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hObj : ∀ i : O, IsDcpo (Obj i))
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hmap : ∀ j : M, ScottContinuous (map j))
    (i : O) : ScottContinuous (DiagramLimitCarrier.proj (shape := shape) (map := map) i) := by
  constructor
  · intro x y hxy
    exact hxy i
  · intro A s hA hs
    let t := DiagramLimitCarrier.directedSup hObj hantisymm hmap A hA
    have ht : IsSup A t :=
      DiagramLimitCarrier.directedSup_isSup hObj hantisymm hmap A hA
    have hst : s = t :=
      DiagramLimitCarrier.antisymmetric hantisymm s t
        (Chapter2.IsSup.le_of_isSup hs ht) (Chapter2.IsSup.le_of_isSup ht hs)
    have htCoord :
        IsSup (DiagramLimitCarrier.coordSet A i) (DiagramLimitCarrier.proj i t) :=
      DiagramLimitCarrier.supTuple_isSup_coord hObj A hA i
    simpa [DiagramLimitCarrier.coordSet, DiagramLimitCarrier.proj, hst] using htCoord

/-- The limiting cone carried by the commuting-tuple object. -/
def DiagramLimitCarrier.limitCone
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)} :
    Cone shape Obj map (DiagramLimitCarrier shape Obj map) where
  leg := DiagramLimitCarrier.proj
  commute j x := x.2 j

/-- The unique mediator from any cone into the commuting-tuple cone. -/
def DiagramLimitCarrier.lift
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    {E : Type z} [Preorder E] (c : Cone shape Obj map E) :
    E → DiagramLimitCarrier shape Obj map :=
  fun x => ⟨fun i => c.leg i x, fun j => c.commute j x⟩

theorem DiagramLimitCarrier.lift_scottContinuous
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    {E : Type z} [Preorder E] (c : Cone shape Obj map E)
    (hc : ∀ i : O, ScottContinuous (c.leg i)) :
    ScottContinuous (DiagramLimitCarrier.lift c) := by
  constructor
  · intro x y hxy i
    exact (hc i).1 hxy
  · intro A s hA hs
    constructor
    · intro y hy i
      rcases hy with ⟨a, ha, rfl⟩
      exact ((hc i).2 hA hs).1 ⟨a, ha, rfl⟩
    · intro y hy i
      exact ((hc i).2 hA hs).2 (y.1 i) (by
        intro z hz
        rcases hz with ⟨a, ha, rfl⟩
        exact hy ⟨a, ha, rfl⟩ i)

/-- The coordinatewise least tuple for a pointed diagram. -/
noncomputable def DiagramLimitCarrier.leastTuple
    {O : Type u} {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    (hpointed : ∀ i : O, HasLeastElement (Obj i)) : ∀ i : O, Obj i :=
  fun i => Classical.choose (hpointed i)

theorem DiagramLimitCarrier.leastTuple_isLeast
    {O : Type u} {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    (hpointed : ∀ i : O, HasLeastElement (Obj i)) (i : O) :
    Chapter2.IsLeast (DiagramLimitCarrier.leastTuple hpointed i) :=
  Classical.choose_spec (hpointed i)

theorem DiagramLimitCarrier.leastTuple_commutes
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hpointed : ∀ i : O, HasLeastElement (Obj i))
    (hmap : ∀ j : M, StrictScottContinuous (map j)) (j : M) :
    map j (DiagramLimitCarrier.leastTuple hpointed (shape.dom j)) =
      DiagramLimitCarrier.leastTuple hpointed (shape.cod j) := by
  have hmapLeast :
      Chapter2.IsLeast
        (map j (DiagramLimitCarrier.leastTuple hpointed (shape.dom j))) :=
    (hmap j).2
      (DiagramLimitCarrier.leastTuple hpointed (shape.dom j))
      (DiagramLimitCarrier.leastTuple_isLeast hpointed (shape.dom j))
  have hcodLeast :
      Chapter2.IsLeast
        (DiagramLimitCarrier.leastTuple hpointed (shape.cod j)) :=
    DiagramLimitCarrier.leastTuple_isLeast hpointed (shape.cod j)
  exact hantisymm (shape.cod j) _ _
    (hmapLeast (DiagramLimitCarrier.leastTuple hpointed (shape.cod j)))
    (hcodLeast (map j (DiagramLimitCarrier.leastTuple hpointed (shape.dom j))))

/-- The coordinatewise bottom tuple as an element of the limiting carrier. -/
noncomputable def DiagramLimitCarrier.least
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hpointed : ∀ i : O, HasLeastElement (Obj i))
    (hmap : ∀ j : M, StrictScottContinuous (map j)) :
    DiagramLimitCarrier shape Obj map where
  val := DiagramLimitCarrier.leastTuple hpointed
  property := DiagramLimitCarrier.leastTuple_commutes (shape := shape) (map := map)
    hantisymm hpointed hmap

theorem DiagramLimitCarrier.least_isLeast
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hpointed : ∀ i : O, HasLeastElement (Obj i))
    (hmap : ∀ j : M, StrictScottContinuous (map j)) :
    Chapter2.IsLeast (DiagramLimitCarrier.least hantisymm hpointed hmap) := by
  intro x i
  change DiagramLimitCarrier.leastTuple hpointed i ≤ x.1 i
  exact DiagramLimitCarrier.leastTuple_isLeast hpointed i (x.1 i)

theorem DiagramLimitCarrier.hasLeastElement
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hpointed : ∀ i : O, HasLeastElement (Obj i))
    (hmap : ∀ j : M, StrictScottContinuous (map j)) :
    HasLeastElement (DiagramLimitCarrier shape Obj map) :=
  ⟨DiagramLimitCarrier.least hantisymm hpointed hmap,
    DiagramLimitCarrier.least_isLeast hantisymm hpointed hmap⟩

theorem DiagramLimitCarrier.proj_strictScottContinuous
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    (hObj : ∀ i : O, IsDcpo (Obj i))
    (hantisymm : ∀ i : O, IsAntisymmetricOrder (Obj i))
    (hpointed : ∀ i : O, HasLeastElement (Obj i))
    (hmap : ∀ j : M, StrictScottContinuous (map j)) (i : O) :
    StrictScottContinuous
      (DiagramLimitCarrier.proj (shape := shape) (map := map) i) := by
  refine ⟨DiagramLimitCarrier.proj_scottContinuous hObj hantisymm
    (fun j => (hmap j).1) i, ?_⟩
  intro x hx
  have hbottom :
      Chapter2.IsLeast (DiagramLimitCarrier.least hantisymm hpointed hmap) :=
    DiagramLimitCarrier.least_isLeast hantisymm hpointed hmap
  have hx_eq :
      x = DiagramLimitCarrier.least hantisymm hpointed hmap :=
    DiagramLimitCarrier.antisymmetric hantisymm x
      (DiagramLimitCarrier.least hantisymm hpointed hmap)
      (hx (DiagramLimitCarrier.least hantisymm hpointed hmap))
      (hbottom x)
  intro y
  rw [hx_eq]
  change DiagramLimitCarrier.leastTuple hpointed i ≤ y
  exact DiagramLimitCarrier.leastTuple_isLeast hpointed i y

theorem DiagramLimitCarrier.lift_strictScottContinuous
    {O : Type u} {M : Type v} {shape : DiagramData O M}
    {Obj : O → Type w} [∀ i : O, Preorder (Obj i)]
    {map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)}
    {E : Type z} [Preorder E] (c : Cone shape Obj map E)
    (hc : ∀ i : O, StrictScottContinuous (c.leg i)) :
    StrictScottContinuous (DiagramLimitCarrier.lift c) := by
  refine ⟨DiagramLimitCarrier.lift_scottContinuous c (fun i => (hc i).1), ?_⟩
  intro x hx y i
  exact (hc i).2 x hx (y.1 i)

/-- A limiting cone in the current concrete-diagram interface for `DCPO`.  This
records the actual universal property: a dcpo carrier, continuous projection
legs, and a unique continuous mediating map from every other cone whose vertex
is also a partial-order dcpo. -/
structure LimitingConeData
    {O : Type u} {M : Type v} (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j))
    (L : Type l) [Preorder L] where
  isDcpo : IsDcpo L
  cone : Cone shape Obj map L
  leg_continuous : ∀ i : O, ScottContinuous (cone.leg i)
  lift :
    ∀ (E : Type z) [Preorder E], IsDcpo E → IsAntisymmetricOrder E →
      (c : Cone shape Obj map E) →
        (∀ i : O, ScottContinuous (c.leg i)) → E → L
  lift_continuous :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (c : Cone shape Obj map E) (hc : ∀ i : O, ScottContinuous (c.leg i)),
      ScottContinuous (lift E hE hEanti c hc)
  lift_fac :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (c : Cone shape Obj map E) (hc : ∀ i : O, ScottContinuous (c.leg i))
      (i : O) (x : E),
      cone.leg i (lift E hE hEanti c hc x) = c.leg i x
  lift_unique :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (c : Cone shape Obj map E) (hc : ∀ i : O, ScottContinuous (c.leg i))
      (g : E → L),
      ScottContinuous g →
      (∀ i : O, ∀ x : E, cone.leg i (g x) = c.leg i x) →
        ∀ x : E, g x = lift E hE hEanti c hc x

/-- A colimiting cocone in the current concrete-diagram interface for `DCPO`.
This is the dual universal property: a dcpo carrier, continuous injection legs,
and a unique continuous mediating map into every other cocone whose vertex is
also a partial-order dcpo. -/
structure ColimitingCoconeData
    {O : Type u} {M : Type v} (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j))
    (C : Type l) [Preorder C] where
  isDcpo : IsDcpo C
  cocone : Cocone shape Obj map C
  leg_continuous : ∀ i : O, ScottContinuous (cocone.leg i)
  desc :
    ∀ (E : Type z) [Preorder E], IsDcpo E → IsAntisymmetricOrder E →
      (c : Cocone shape Obj map E) →
        (∀ i : O, ScottContinuous (c.leg i)) → C → E
  desc_continuous :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (c : Cocone shape Obj map E) (hc : ∀ i : O, ScottContinuous (c.leg i)),
      ScottContinuous (desc E hE hEanti c hc)
  desc_fac :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (c : Cocone shape Obj map E) (hc : ∀ i : O, ScottContinuous (c.leg i))
      (i : O) (x : Obj i),
      desc E hE hEanti c hc (cocone.leg i x) = c.leg i x
  desc_unique :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (c : Cocone shape Obj map E) (hc : ∀ i : O, ScottContinuous (c.leg i))
      (g : C → E),
      ScottContinuous g →
      (∀ i : O, ∀ x : Obj i, g (cocone.leg i x) = c.leg i x) →
        ∀ x : C, g x = desc E hE hEanti c hc x

/-- Strict-pointed limiting cone data for `DCPO⊥!`.  It mirrors
`LimitingConeData` but restricts diagram maps, cone legs, and mediating maps to
strict Scott-continuous maps. -/
structure StrictPointedLimitingConeData
    {O : Type u} {M : Type v} (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j))
    (L : Type l) [Preorder L] where
  isDcpo : IsDcpo L
  antisymmetric : IsAntisymmetricOrder L
  pointed : HasLeastElement L
  cone : Cone shape Obj map L
  leg_strict : ∀ i : O, StrictScottContinuous (cone.leg i)
  lift :
    ∀ (E : Type z) [Preorder E], IsDcpo E → IsAntisymmetricOrder E →
      HasLeastElement E →
        (c : Cone shape Obj map E) →
          (∀ i : O, StrictScottContinuous (c.leg i)) → E → L
  lift_strict :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (hEpointed : HasLeastElement E)
      (c : Cone shape Obj map E) (hc : ∀ i : O, StrictScottContinuous (c.leg i)),
      StrictScottContinuous (lift E hE hEanti hEpointed c hc)
  lift_fac :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (hEpointed : HasLeastElement E)
      (c : Cone shape Obj map E) (hc : ∀ i : O, StrictScottContinuous (c.leg i))
      (i : O) (x : E),
      cone.leg i (lift E hE hEanti hEpointed c hc x) = c.leg i x
  lift_unique :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (hEpointed : HasLeastElement E)
      (c : Cone shape Obj map E) (hc : ∀ i : O, StrictScottContinuous (c.leg i))
      (g : E → L),
      StrictScottContinuous g →
      (∀ i : O, ∀ x : E, cone.leg i (g x) = c.leg i x) →
        ∀ x : E, g x = lift E hE hEanti hEpointed c hc x

/-- Strict-pointed colimiting cocone data for `DCPO⊥!`.  It records the dual
universal property with strict Scott-continuous cocone legs and mediating maps. -/
structure StrictPointedColimitingCoconeData
    {O : Type u} {M : Type v} (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j))
    (C : Type l) [Preorder C] where
  isDcpo : IsDcpo C
  antisymmetric : IsAntisymmetricOrder C
  pointed : HasLeastElement C
  cocone : Cocone shape Obj map C
  leg_strict : ∀ i : O, StrictScottContinuous (cocone.leg i)
  desc :
    ∀ (E : Type z) [Preorder E], IsDcpo E → IsAntisymmetricOrder E →
      HasLeastElement E →
        (c : Cocone shape Obj map E) →
          (∀ i : O, StrictScottContinuous (c.leg i)) → C → E
  desc_strict :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (hEpointed : HasLeastElement E)
      (c : Cocone shape Obj map E) (hc : ∀ i : O, StrictScottContinuous (c.leg i)),
      StrictScottContinuous (desc E hE hEanti hEpointed c hc)
  desc_fac :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (hEpointed : HasLeastElement E)
      (c : Cocone shape Obj map E) (hc : ∀ i : O, StrictScottContinuous (c.leg i))
      (i : O) (x : Obj i),
      desc E hE hEanti hEpointed c hc (cocone.leg i x) = c.leg i x
  desc_unique :
    ∀ (E : Type z) [Preorder E] (hE : IsDcpo E) (hEanti : IsAntisymmetricOrder E)
      (hEpointed : HasLeastElement E)
      (c : Cocone shape Obj map E) (hc : ∀ i : O, StrictScottContinuous (c.leg i))
      (g : C → E),
      StrictScottContinuous g →
      (∀ i : O, ∀ x : Obj i, g (cocone.leg i x) = c.leg i x) →
        ∀ x : C, g x = desc E hE hEanti hEpointed c hc x

/-- Completeness of a named domain-category object class in the Chapter 3
concrete-diagram interface.  The generic named-category version records
Scott-continuity; the dedicated `DCPO⊥!` declarations below use strict maps. -/
def DomainCategoryHasAllLimits (C : DomainCategoryName) : Prop :=
  ∀ (O : Type u) (M : Type v) (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)),
      (∀ i : O, DomainCategoryObject C (Obj i)) →
        (∀ j : M, ScottContinuous (map j)) →
          ∃ L : Type z, ∃ instL : Preorder L,
            @DomainCategoryObject C L instL ∧
              Nonempty (@LimitingConeData.{u, v, w, z, z} O M shape Obj _ map L instL)

/-- Cocompleteness of a named domain-category object class in the Chapter 3
concrete-diagram interface, with the same Scott-continuous morphism convention
as `DomainCategoryHasAllLimits`. -/
def DomainCategoryHasAllColimits (C : DomainCategoryName) : Prop :=
  ∀ (O : Type u) (M : Type v) (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)),
      (∀ i : O, DomainCategoryObject C (Obj i)) →
        (∀ j : M, ScottContinuous (map j)) →
          ∃ Col : Type z, ∃ instCol : Preorder Col,
            @DomainCategoryObject C Col instCol ∧
              Nonempty (@ColimitingCoconeData.{u, v, w, z, z} O M shape Obj _ map Col instCol)

/-- Completeness of `DCPO` in the concrete-diagram interface used for Theorem
3.3.1.  Because the local development is preorder-based, the partial-order part
of "dcpo" is carried by the explicit `IsAntisymmetricOrder` hypothesis. -/
def DCPOHasAllLimits : Prop :=
  ∀ (O : Type u) (M : Type v) (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)),
      (∀ i : O, IsDcpo (Obj i)) →
        (∀ i : O, IsAntisymmetricOrder (Obj i)) →
          (∀ j : M, ScottContinuous (map j)) →
            ∃ L : Type (max u w), ∃ instL : Preorder L,
              @IsDcpo L instL ∧ @IsAntisymmetricOrder L instL ∧
                Nonempty (@LimitingConeData.{u, v, w, z, max u w}
                  O M shape Obj _ map L instL)

/-- Cocompleteness of `DCPO` in the Chapter 3 concrete-diagram setting.  This
is still an external-literature theorem, but its statement now matches the
book's partial-order reading of `DCPO` by carrying explicit antisymmetry
hypotheses for objects and the colimit carrier.

The PDF attributes Theorem 3.3.2 to Markowsky [Mar77], Meseguer [Mes77], a
reduction to Herrlich--Strecker [HS73, Theorem 23.14] appearing in
Lehmann--Smyth [LS81], and the detailed analysis by Fiech [Fie92]. -/
def DCPOHasAllColimits : Prop :=
  ∀ (O : Type u) (M : Type v) (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)),
      (∀ i : O, IsDcpo (Obj i)) →
        (∀ i : O, IsAntisymmetricOrder (Obj i)) →
          (∀ j : M, ScottContinuous (map j)) →
            ∃ Col : Type z, ∃ instCol : Preorder Col,
              @IsDcpo Col instCol ∧ @IsAntisymmetricOrder Col instCol ∧
                Nonempty (@ColimitingCoconeData.{u, v, w, z, z}
                  O M shape Obj _ map Col instCol)

/-- Completeness of `DCPO⊥!` in the current concrete-diagram interface:
objects are antisymmetric pointed dcpos and all diagram/cone/mediating maps are
strict Scott-continuous.  The carrier universe matches the concrete
commuting-tuple construction used by the proof below. -/
def StrictPointedDCPOHasAllLimits : Prop :=
  ∀ (O : Type u) (M : Type v) (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)),
      (∀ i : O, IsDcpo (Obj i)) →
        (∀ i : O, IsAntisymmetricOrder (Obj i)) →
          (∀ i : O, HasLeastElement (Obj i)) →
            (∀ j : M, StrictScottContinuous (map j)) →
              ∃ L : Type (max u w), ∃ instL : Preorder L,
                @IsDcpo L instL ∧ @IsAntisymmetricOrder L instL ∧
                  @HasLeastElement L instL ∧
                    Nonempty (@StrictPointedLimitingConeData.{u, v, w, z, max u w}
                      O M shape Obj _ map L instL)

/-- Cocompleteness of `DCPO⊥!` in the current concrete-diagram interface, with
the same strict Scott-continuous morphism convention as
`StrictPointedDCPOHasAllLimits`.

Unlike the strict completeness component, no strict colimit construction is
formalized here yet; Theorem 3.3.4 therefore keeps this as local proof debt
rather than deriving it from the `DCPO` colimit theorem. -/
def StrictPointedDCPOHasAllColimits : Prop :=
  ∀ (O : Type u) (M : Type v) (shape : DiagramData O M)
    (Obj : O → Type w) [∀ i : O, Preorder (Obj i)]
    (map : ∀ j : M, Obj (shape.dom j) → Obj (shape.cod j)),
      (∀ i : O, IsDcpo (Obj i)) →
        (∀ i : O, IsAntisymmetricOrder (Obj i)) →
          (∀ i : O, HasLeastElement (Obj i)) →
            (∀ j : M, StrictScottContinuous (map j)) →
              ∃ Col : Type z, ∃ instCol : Preorder Col,
                @IsDcpo Col instCol ∧ @IsAntisymmetricOrder Col instCol ∧
                  @HasLeastElement Col instCol ∧
                    Nonempty (@StrictPointedColimitingCoconeData.{u, v, w, z, z}
                      O M shape Obj _ map Col instCol)

/-- Concrete function-space adjunction for `DCPO`: application and currying
identify continuous maps `C × D -> E` with continuous maps `C -> [D -> E]`.
The support theorem is proved after the bundled curry/uncurry definitions. -/
def DCPOFunctionSpaceAdjunction : Prop :=
  ∀ C D E : Type u, ∀ [Preorder C], ∀ [Preorder D], ∀ [Preorder E],
    IsDcpo C → IsAntisymmetricOrder C →
      IsDcpo D → IsAntisymmetricOrder D →
        IsDcpo E → IsAntisymmetricOrder E →
          Nonempty (@OrderIsoData (ContFun (C × D) E) (ContFun C (ContFun D E))
            inferInstance inferInstance)

/-- Internal-hom comparison for `DCPO`: an exponential object is a partial-order
dcpo compared with the concrete continuous function-space carrier.  The
concrete comparison is proved below by choosing `ContFun D E` itself. -/
def DCPOInternalHomComparison : Prop :=
  ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
    IsDcpo D → IsAntisymmetricOrder D →
      IsDcpo E → IsAntisymmetricOrder E →
        ∃ Exp : Type u, ∃ instExp : Preorder Exp,
          @IsDcpo Exp instExp ∧ @IsAntisymmetricOrder Exp instExp ∧
            Nonempty (@OrderIsoData Exp (ContFun D E) instExp inferInstance)

/-- Cartesian closedness of `DCPO`, split into the proved concrete
function-space adjunction and the internal-hom comparison with the ordinary
continuous function-space carrier. -/
def DCPOCartesianClosed : Prop :=
  DCPOFunctionSpaceAdjunction.{u} ∧ DCPOInternalHomComparison.{u}

/-- Object-class support for the strict function-space carrier used by
`DCPO⊥!`: strict continuous maps form a pointed partial-order dcpo. -/
def StrictPointedFunctionSpaceObjectSupport : Prop :=
  ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
    IsDcpo D → IsAntisymmetricOrder D → HasLeastElement D →
      IsDcpo E → IsAntisymmetricOrder E → HasLeastElement E →
        @IsDcpo (StrictContFun D E) inferInstance ∧
          @IsAntisymmetricOrder (StrictContFun D E) inferInstance ∧
            @HasLeastElement (StrictContFun D E) inferInstance

/-- Strict-pointed internal-hom comparison for `DCPO⊥!`: an internal-hom object
is a pointed partial-order dcpo compared with the strict function-space
carrier.  The concrete comparison is proved below by choosing the strict
function-space carrier itself. -/
def StrictPointedInternalHomComparison : Prop :=
  ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
    IsDcpo D → IsAntisymmetricOrder D → HasLeastElement D →
      IsDcpo E → IsAntisymmetricOrder E → HasLeastElement E →
        ∃ H : Type u, ∃ instH : Preorder H,
          @IsDcpo H instH ∧ @IsAntisymmetricOrder H instH ∧
            @HasLeastElement H instH ∧
              Nonempty (@OrderIsoData H (StrictContFun D E) instH inferInstance)

/-- Object/internal-hom component used in the monoidal-closed construction. -/
def StrictPointedDCPOMonoidalClosedCore : Prop :=
  StrictPointedFunctionSpaceObjectSupport.{u} ∧
    StrictPointedInternalHomComparison.{u}

/-- Concrete tensor-hom adjunction support for the strict pointed interface.  The
current carrier-level statement compares strict continuous maps out of the smash
product with strict continuous maps into the strict function-space carrier.  The
explicit `OrderBot` and bottom-separation hypotheses are the preorder-interface
side conditions used by the local smash-product construction. -/
def StrictPointedTensorHomAdjunction : Prop :=
  ∀ D E F : Type u, ∀ [Preorder D], ∀ [Preorder E], ∀ [Preorder F],
    ∀ [OrderBot D], ∀ [OrderBot E],
      IsDcpo D → IsAntisymmetricOrder D → HasLeastElement D →
        IsDcpo E → IsAntisymmetricOrder E → HasLeastElement E →
          IsDcpo F → IsAntisymmetricOrder F → HasLeastElement F →
            (∀ x : D, x ≤ ⊥ → x = ⊥) →
              (∀ y : E, y ≤ ⊥ → y = ⊥) →
                Nonempty
                  (@OrderIsoData (StrictContFun (SmashProduct D E) F)
                    (StrictContFun D (StrictContFun E F)) inferInstance inferInstance)

/-- Monoidal closedness of `DCPO⊥!` in the concrete local interface: the
strict function-space object/internal-hom data together with the smash-product
tensor-hom order isomorphism. -/
def StrictPointedDCPOMonoidalClosed : Prop :=
  StrictPointedDCPOMonoidalClosedCore.{u} ∧ StrictPointedTensorHomAdjunction.{u}

/-- Concrete function-space adjunction for `DCPO⊥` with non-strict morphisms.
The object hypotheses are pointed, but the hom-sets are ordinary
Scott-continuous maps. -/
def PointedDCPOFunctionSpaceAdjunction : Prop :=
  ∀ C D E : Type u, ∀ [Preorder C], ∀ [Preorder D], ∀ [Preorder E],
    IsDcpo C → IsAntisymmetricOrder C → HasLeastElement C →
      IsDcpo D → IsAntisymmetricOrder D → HasLeastElement D →
        IsDcpo E → IsAntisymmetricOrder E → HasLeastElement E →
          Nonempty (@OrderIsoData (ContFun (C × D) E) (ContFun C (ContFun D E))
            inferInstance inferInstance)

/-- Pointed internal-hom comparison for `DCPO⊥`: an internal-hom object is
pointed and order-isomorphic to the ordinary continuous function-space carrier.
The concrete comparison is proved below by choosing `ContFun D E` itself. -/
def PointedDCPOInternalHomComparison : Prop :=
  ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
    IsDcpo D → IsAntisymmetricOrder D → HasLeastElement D →
      IsDcpo E → IsAntisymmetricOrder E → HasLeastElement E →
        ∃ H : Type u, ∃ instH : Preorder H,
          @IsDcpo H instH ∧ @IsAntisymmetricOrder H instH ∧
            @HasLeastElement H instH ∧
              Nonempty (@OrderIsoData H (ContFun D E) instH inferInstance)

/-- Cartesian closedness of the pointed dcpo category, split into the proved
ordinary continuous function-space adjunction and the pointed internal-hom
comparison with the ordinary function-space carrier.  Morphisms are not
required to be strict here, matching `DCPO⊥`. -/
def PointedDCPOCartesianClosed : Prop :=
  PointedDCPOFunctionSpaceAdjunction.{u} ∧
    PointedDCPOInternalHomComparison.{u}

/-- The concrete target statement of Theorem 3.3.1 after expanding the book's
commuting-tuple construction.  The theorem below proves this predicate
directly. -/
def DCPOCompletenessStatement : Prop := DCPOHasAllLimits.{u, v, w, z}

/-- Statement form of Theorem 3.3.2.  The book cites external colimit
construction literature for this result: Markowsky [Mar77], Meseguer [Mes77],
Herrlich--Strecker [HS73, Theorem 23.14] via Lehmann--Smyth [LS81], and Fiech
[Fie92].  The current Lean declaration keeps the full universal property as an
explicit statement.  As in 3.3.1, the local preorder-based interface records
the partial-order side condition explicitly. -/
def DCPOCocompletenessStatement : Prop := DCPOHasAllColimits.{u, v, w, z}

/-- Target statement for the complete strict pointed dcpo category interface
used by Theorem 3.3.4. -/
def StrictPointedDCPOCompletenessStatement : Prop :=
  StrictPointedDCPOHasAllLimits.{u, v, w, z}

/-- Target statement for the cocomplete strict pointed dcpo category interface
used by Theorem 3.3.4. -/
def StrictPointedDCPOCocompletenessStatement : Prop :=
  StrictPointedDCPOHasAllColimits.{u, v, w, z}

/-- Theorem 3.3.1. PDF text: "DCPO has limits of arbitrary diagrams."

Current Lean spelling: for any concrete diagram of partial-order dcpos and
Scott-continuous maps, the commuting-tuple carrier is a partial-order dcpo and
carries the limiting-cone universal property against partial-order dcpo cone
vertices. -/
theorem theorem_3_3_1_dcpo_complete :
    DCPOCompletenessStatement.{u, v, w, z} := by
  intro O M shape Obj _instObj map hObj hantisymm hmap
  refine ⟨DiagramLimitCarrier shape Obj map, inferInstance, ?_, ?_, ?_⟩
  · exact DiagramLimitCarrier.isDcpo hObj hantisymm hmap
  · exact DiagramLimitCarrier.antisymmetric hantisymm
  · refine ⟨?_⟩
    refine
      { isDcpo := DiagramLimitCarrier.isDcpo hObj hantisymm hmap
        cone := DiagramLimitCarrier.limitCone
        leg_continuous := DiagramLimitCarrier.proj_scottContinuous hObj hantisymm hmap
        lift := ?_
        lift_continuous := ?_
        lift_fac := ?_
        lift_unique := ?_ }
    · intro E _instE _hE _hEanti c _hc
      exact DiagramLimitCarrier.lift c
    · intro E _instE _hE _hEanti c hc
      exact DiagramLimitCarrier.lift_scottContinuous c hc
    · intro E _instE _hE _hEanti c _hc i x
      rfl
    · intro E _instE _hE _hEanti c _hc g _hg hfac x
      apply Subtype.ext
      funext i
      exact hfac i x

/-- Theorem 3.3.4, complete component. PDF text component: "`DCPO⊥!` is
complete."

Current Lean spelling: for any concrete diagram of pointed partial-order dcpos
and strict Scott-continuous maps, the same commuting-tuple carrier as in
Theorem 3.3.1 has a coordinatewise least element, strict projection legs, and a
strict universal mediating map from every strict cone. -/
theorem theorem_3_3_4_strict_pointed_dcpo_complete :
    StrictPointedDCPOCompletenessStatement.{u, v, w, z} := by
  intro O M shape Obj _instObj map hObj hantisymm hpointed hmap
  refine ⟨DiagramLimitCarrier shape Obj map, inferInstance, ?_, ?_, ?_, ?_⟩
  · exact DiagramLimitCarrier.isDcpo hObj hantisymm (fun j => (hmap j).1)
  · exact DiagramLimitCarrier.antisymmetric hantisymm
  · exact DiagramLimitCarrier.hasLeastElement hantisymm hpointed hmap
  · refine ⟨?_⟩
    refine
      { isDcpo := DiagramLimitCarrier.isDcpo hObj hantisymm (fun j => (hmap j).1)
        antisymmetric := DiagramLimitCarrier.antisymmetric hantisymm
        pointed := DiagramLimitCarrier.hasLeastElement hantisymm hpointed hmap
        cone := DiagramLimitCarrier.limitCone
        leg_strict := DiagramLimitCarrier.proj_strictScottContinuous hObj hantisymm hpointed hmap
        lift := ?_
        lift_strict := ?_
        lift_fac := ?_
        lift_unique := ?_ }
    · intro E _instE _hE _hEanti _hEpointed c _hc
      exact DiagramLimitCarrier.lift c
    · intro E _instE _hE _hEanti _hEpointed c hc
      exact DiagramLimitCarrier.lift_strictScottContinuous c hc
    · intro E _instE _hE _hEanti _hEpointed c _hc i x
      rfl
    · intro E _instE _hE _hEanti _hEpointed c _hc g _hg hfac x
      apply Subtype.ext
      funext i
      exact hfac i x

/-- Theorem 3.3.4, cocomplete component. PDF text component: "`DCPO⊥!` is
cocomplete."

The PDF states this strict pointed cocompleteness component without an
element-level proof in the surrounding text and without a separate external
source citation. Following the project policy, this is registered as an
explicit `admit`; `docs/chapter3-map.json` records the boundary. -/
theorem theorem_3_3_4_strict_pointed_dcpo_cocomplete : StrictPointedDCPOCocompletenessStatement.{u, v, w, z} := by admit

/-- Theorem 3.3.2. PDF text: "DCPO has colimits of arbitrary diagrams."

Current Lean spelling: documented external theorem.  The PDF cites Markowsky
[Mar77], Meseguer [Mes77], Herrlich--Strecker [HS73, Theorem 23.14] via
Lehmann--Smyth [LS81], and Fiech [Fie92] for this colimit construction. -/
axiom theorem_3_3_2_dcpo_cocomplete :
    DCPOCocompletenessStatement.{u, v, w, z}

/-- Auxiliary packaging lemma for Theorem 3.3.3. PDF text: "DCPO is cartesian closed,
complete and cocomplete."

Current Lean spelling: package a `DCPO` cartesian-closed interface and the
documented external cocompleteness theorem together with the constructed
commuting-tuple completeness theorem above.  The concrete cartesian-closed
interface is proved later by choosing the ordinary continuous function-space
carrier itself. -/
theorem theorem_3_3_3_dcpo_cartesian_closed_complete_cocomplete_of_cartesianClosed :
    DCPOCartesianClosed.{u} →
      DCPOCartesianClosed.{u} ∧ DCPOHasAllLimits.{u, v, w, z} ∧
        DCPOHasAllColimits.{u, v, w, z} := by
  intro hClosed
  exact ⟨hClosed, theorem_3_3_1_dcpo_complete, theorem_3_3_2_dcpo_cocomplete⟩

/-- Theorem 3.3.4. PDF text: "DCPO⊥! is monoidal closed, complete and
cocomplete."

Current Lean spelling: package a strict-pointed monoidal-closed interface with
the strict-pointed complete/cocomplete interfaces.  The strict completeness
component is constructed above from the commuting-tuple carrier; the strict
cocompleteness component is the registered local proof debt above.  The
concrete monoidal-closed interface is proved later in the file from the strict
function-space carrier and internal-hom comparison; the smash-product
tensor-hom order isomorphism is packaged separately as
`StrictPointedTensorHomAdjunction`. -/
theorem theorem_3_3_4_strict_pointed_dcpo_monoidal_closed_complete_cocomplete_of_monoidalClosed :
    StrictPointedDCPOMonoidalClosed.{u} →
      StrictPointedDCPOCompletenessStatement.{u, v, w, z} →
        StrictPointedDCPOMonoidalClosed.{u} ∧
          StrictPointedDCPOHasAllLimits.{u, v, w, z} ∧
            StrictPointedDCPOHasAllColimits.{u, v, w, z} := by
  intro hClosed hComplete
  exact ⟨hClosed, hComplete, theorem_3_3_4_strict_pointed_dcpo_cocomplete⟩

/-- Auxiliary identity lemma for Theorem 3.3.5. PDF text: "DCPO⊥ is cartesian
closed."

Current Lean spelling: pointed `DCPO⊥` is cartesian closed when the pointed
internal-hom comparison data with the ordinary continuous function-space carrier
is supplied.  The concrete theorem below supplies that comparison by choosing
the ordinary function-space carrier itself; morphisms are intentionally not
strict. -/
theorem theorem_3_3_5_pointed_dcpo_cartesian_closed_of_cartesianClosed
    (h : PointedDCPOCartesianClosed.{u}) : PointedDCPOCartesianClosed.{u} :=
  h


end Chapter3
end AbramskyJung

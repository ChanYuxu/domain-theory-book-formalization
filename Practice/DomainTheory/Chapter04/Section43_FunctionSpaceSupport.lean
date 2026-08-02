import Practice.DomainTheory.Chapter04.Section43_ForbiddenRetracts

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Function-space support for Lemma 4.3.1

Generic Scott-open step-function lemmas used by the forbidden-shape branches.
-/

universe u

namespace AbramskyJung
namespace Chapter4

/-- A Scott-open step function bundled as a continuous map. -/
noncomputable def OpenStepContFun
    {D E : Type u} [Preorder D] [Preorder E] [OrderBot E]
    (O : ScottOpenCarrier ({ carrier := D, preorder := inferInstance } : OrderedDomain))
    (e : E) : Chapter3.ContFun D E where
  toFun := OpenStepFunction O.carrierSet e
  continuous := openStepFunction_scottContinuous O.scott_open e

/-- The open-set version of Proposition 4.0.2(2): compactness of the value and
way-below containment of the support make an open step approximate every map
lying above the corresponding larger step. -/
theorem openStepContFun_wayBelow
    {D E : Type u} [Preorder D] [Preorder E] [OrderBot E]
    (hE : Chapter3.IsDcpo E)
    {O U : ScottOpenCarrier
      ({ carrier := D, preorder := inferInstance } : OrderedDomain)}
    {e : E} (he : Chapter3.Compact e)
    (hOU : Chapter3.WayBelow O U)
    (f : Chapter3.ContFun D E)
    (hStep : OpenStepContFun U e ≤ f) :
    OpenStepContFun O e ≪ f := by
  classical
  intro G s hG hs hfs
  let W : Chapter3.ContFun D E →
      ScottOpenCarrier
        ({ carrier := D, preorder := inferInstance } : OrderedDomain) := fun g =>
    { carrierSet := {x : D | e ≤ g x}
      scott_open := by
        constructor
        · intro x y hy hxy hx
          exact hy (le_trans hx (g.continuous.1 hxy))
        · intro A a hA hAcompl ha haUpper
          have hImageSup :
              Chapter3.IsSup ((fun x : D => g x) '' A) (g a) :=
            g.continuous.2 hA ha
          rcases he (Chapter2.DirectedSet.image g.continuous.1 hA)
              hImageSup haUpper with ⟨ga, hga, hega⟩
          rcases hga with ⟨x, hxA, rfl⟩
          exact (hAcompl hxA) hega }
  have hWMonotone : Monotone W := by
    intro g k hgk x hx
    exact le_trans hx (hgk x)
  have hWDirected : Chapter3.DirectedSet (W '' G) :=
    Chapter2.DirectedSet.image hWMonotone hG
  let S : ScottOpenCarrier
      ({ carrier := D, preorder := inferInstance } : OrderedDomain) :=
    { carrierSet := ⋃ V : W '' G, V.1.carrierSet
      scott_open := Chapter2.scottOpen_iUnion (fun V : W '' G => V.1.scott_open) }
  have hWSup : Chapter3.IsSup (W '' G) S := by
    constructor
    · intro V hV x hx
      change x ∈ ⋃ V : W '' G, V.1.carrierSet
      rw [Set.mem_iUnion]
      exact ⟨⟨V, hV⟩, hx⟩
    · intro V hV x hx
      change x ∈ ⋃ V' : W '' G, V'.1.carrierSet at hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨V', hxV'⟩
      exact hV V'.2 hxV'
  have hUS : U ≤ S := by
    intro x hxU
    have hefx : e ≤ f x := by
      exact le_trans (by
        simpa [OpenStepContFun, OpenStepFunction, hxU] using hStep x) le_rfl
    have hesx : e ≤ s x := le_trans hefx (hfs x)
    have hEvalSup :
        Chapter3.IsSup ((fun g : Chapter3.ContFun D E => g x) '' G) (s x) :=
      (Chapter3.ContFun.eval_scottContinuous hE x).2 hG hs
    rcases he (Chapter3.ContFun.eval_directed hG x) hEvalSup hesx with
      ⟨gx, hgx, heg⟩
    rcases hgx with ⟨g, hg, rfl⟩
    change x ∈ ⋃ V : W '' G, V.1.carrierSet
    rw [Set.mem_iUnion]
    exact ⟨⟨W g, ⟨g, hg, rfl⟩⟩, heg⟩
  rcases hOU hWDirected hWSup hUS with ⟨V, hV, hOV⟩
  rcases hV with ⟨g, hg, rfl⟩
  refine ⟨g, hg, ?_⟩
  intro x
  by_cases hxO : x ∈ O.carrierSet
  · simpa [OpenStepContFun, OpenStepFunction, hxO] using hOV hxO
  · simp [OpenStepContFun, OpenStepFunction, hxO]

end Chapter4
end AbramskyJung

import Practice.DomainTheory.Chapter04.Section43_Core

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Forbidden retracts for Section 4.3.1

Source-facing descriptions of domains `A` (Figure 12) and `X` (Figure 11),
followed by the exact omitted boundary from Exercise 4.3.11(3).
-/

universe u

namespace AbramskyJung
namespace Chapter4

/-- Points of the Figure 12 `A` diagram.  The index order runs down the chain,
so a larger index denotes a strictly smaller common upper bound. -/
inductive Figure12APoint (I : Type u) where
  | bottom
  | left
  | right
  | chain (i : I)
deriving DecidableEq

/-- The order displayed by Figure 12 for domain `A`. -/
def Figure12ALe {I : Type u} (leI : I → I → Prop) :
    Figure12APoint I → Figure12APoint I → Prop
  | .bottom, _ => True
  | .left, .left => True
  | .right, .right => True
  | .left, .chain _ => True
  | .right, .chain _ => True
  | .chain i, .chain j => leI j i
  | _, _ => False

/-- A domain has exactly the order shape `A` from Figure 12.  The chain index
has a first point (`c₀`) and no greatest index, allowing the transfinite version
explicitly mentioned in the proof of Lemma 4.3.1. -/
structure Figure12ADiagram (A : OrderedDomain.{u}) where
  Index : Type u
  indexOrder : LinearOrder Index
  indexLeast : ∃ i₀ : Index, ∀ i : Index, indexOrder.le i₀ i
  indexNoMax : ∀ i : Index, ∃ j : Index, indexOrder.lt i j
  point : Figure12APoint Index → A.carrier
  point_bijective : Function.Bijective point
  order_iff : ∀ x y, point x ≤ point y ↔ Figure12ALe indexOrder.le x y

/-- The six indices `⊥, a, b, c₁, c₂, ⊤` of Figure 11's domain `X`. -/
def Figure11XLe (i j : Fin 6) : Prop :=
  i = 0 ∨ i = j ∨ j = 5 ∨
    ((i = 1 ∨ i = 2) ∧ (j = 3 ∨ j = 4))

/-- A domain has exactly the finite order shape `X` from Figure 11. -/
structure Figure11XDiagram (X : OrderedDomain.{u}) where
  point : Fin 6 → X.carrier
  point_bijective : Function.Bijective point
  order_iff : ∀ i j, point i ≤ point j ↔ Figure11XLe i j

/-- The forbidden-retract alternative used in Lemma 4.3.1: the target contains
either Figure 12's `A` (with a possibly transfinite descending chain) or Figure
11's finite `X` as a continuous retract. -/
def HasForbiddenLDomainRetract (E : OrderedDomain.{u}) : Prop :=
  (∃ A : OrderedDomain.{u}, Nonempty (Figure12ADiagram A) ∧ IsContinuousRetractOf A E) ∨
    (∃ X : OrderedDomain.{u}, Nonempty (Figure11XDiagram X) ∧ IsContinuousRetractOf X E)

/-- Exercise 4.3.11(3), the exact book-omission boundary needed by Lemma
4.3.1: a pointed continuous non-L-domain contains `A` or `X` as a retract.

The textbook explicitly leaves this forbidden-substructure characterization
as an exercise, so the project policy records it as `admit`, not `axiom` or
source-proof `sorry`. -/
theorem exercise_4_3_11_3_non_l_forbidden_retract
    (E : OrderedDomain.{u}) (hE : IsPointedContinuousDomain E)
    (hNotL : ¬ IsLDomain E) :
    HasForbiddenLDomainRetract E := by
  admit

/-- The order-theoretic obstruction used by both corrected source cases: two
elements approximate `f`, but no single approximant of `f` lies above both. -/
def HasBinaryApproximationObstruction {P : Type u} [Preorder P] : Prop :=
  ∃ f f₁ f₂ : P,
    f₁ ≪ f ∧ f₂ ≪ f ∧
      ∀ g : P, g ≪ f → ¬ (f₁ ≤ g ∧ f₂ ≤ g)

/-- A continuous domain cannot contain a binary approximation obstruction.
This is the formal version of the sentence "approximating sets are directed"
used in both cases of the textbook proof. -/
theorem not_continuousDomain_of_binaryApproximationObstruction
    {P : Type u} [Preorder P] (h : HasBinaryApproximationObstruction (P := P)) :
    ¬ Chapter3.IsContinuousDomain P := by
  intro hContinuous
  rcases hContinuous with ⟨B, hBasis⟩
  rcases h with ⟨f, f₁, f₂, hf₁, hf₂, hNoCommon⟩
  have hApproxDir : Chapter2.DirectedSet (Chapter2.Approximants B f) :=
    (hBasis f).1
  have hApproxSup : Chapter2.IsSup (Chapter2.Approximants B f) f :=
    (hBasis f).2
  rcases hf₁ hApproxDir hApproxSup le_rfl with ⟨g₁, hg₁, hf₁g₁⟩
  rcases hf₂ hApproxDir hApproxSup le_rfl with ⟨g₂, hg₂, hf₂g₂⟩
  rcases hApproxDir.2 hg₁ hg₂ with ⟨g, hg, hg₁g, hg₂g⟩
  exact hNoCommon g hg.2
    ⟨le_trans hf₁g₁ hg₁g, le_trans hf₂g₂ hg₂g⟩

/-- Postcomposition by a Scott-continuous map is Scott-continuous on continuous
function spaces equipped with the pointwise order. -/
def postcomposeContFun
    {D A E : Type u} [Preorder D] [Preorder A] [Preorder E]
    (k : Chapter3.ContFun A E) :
    Chapter3.ContFun D A → Chapter3.ContFun D E :=
  fun f => Chapter3.ContFun.comp k f

theorem postcomposeContFun_scottContinuous
    {D A E : Type u} [Preorder D] [Preorder A] [Preorder E]
    (hA : Chapter3.IsDcpo A) (k : Chapter3.ContFun A E) :
    Chapter3.ScottContinuous (postcomposeContFun (D := D) k) := by
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

/-- A continuous retract in the codomain induces a continuous retract between
the corresponding continuous-function spaces.  This is the formal version of
the retract observation made immediately before the two cases of Lemma 4.3.1. -/
def continuousFunctionSpaceRetract
    {D A E : Type u} [Preorder D] [Preorder A] [Preorder E]
    (sr : Chapter3.ContinuousSectionRetractionPair A E)
    (hA : Chapter3.IsDcpo A) (hE : Chapter3.IsDcpo E) :
    Chapter3.ContinuousSectionRetractionPair
      (Chapter3.ContFun D A) (Chapter3.ContFun D E) where
  s := postcomposeContFun
    ({ toFun := sr.s, continuous := sr.continuous_s } : Chapter3.ContFun A E)
  r := postcomposeContFun
    ({ toFun := sr.r, continuous := sr.continuous_r } : Chapter3.ContFun E A)
  monotone_s := (postcomposeContFun_scottContinuous hA
    ({ toFun := sr.s, continuous := sr.continuous_s } : Chapter3.ContFun A E)).1
  monotone_r := (postcomposeContFun_scottContinuous hE
    ({ toFun := sr.r, continuous := sr.continuous_r } : Chapter3.ContFun E A)).1
  retract := by
    intro f
    apply Chapter3.ContFun.ext_apply
    intro x
    exact sr.retract (f x)
  continuous_s := postcomposeContFun_scottContinuous hA
    ({ toFun := sr.s, continuous := sr.continuous_s } : Chapter3.ContFun A E)
  continuous_r := postcomposeContFun_scottContinuous hE
    ({ toFun := sr.r, continuous := sr.continuous_r } : Chapter3.ContFun E A)

end Chapter4
end AbramskyJung

import Practice.DomainTheory.Chapter04.Section43_Figure11Core

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# The Figure 11 function-space obstruction for Lemma 4.3.1

The corrected cover family and the final contradiction for source Case 2.
-/

universe u

namespace AbramskyJung
namespace Chapter4

/-- The corrected Case 2 family member.  It takes `⊤` on the selected cover
member, `c₂` on the rest of the intersection, and agrees with `g` outside. -/
noncomputable def Figure11CoverFunction
    {D : Type u} [Preorder D] {X : OrderedDomain.{u}}
    (hX : Figure11XDiagram X) (g : Chapter3.ContFun D X.carrier)
    (I V : ScottOpenCarrier
      ({ carrier := D, preorder := inferInstance } : OrderedDomain)) :
    D → X.carrier := by
  classical
  exact fun x =>
    if x ∈ I.carrierSet then
      if x ∈ V.carrierSet then hX.point 5 else hX.point 4
    else g x

theorem figure11Pair_c₁_le_c₂_outside_inter
    {D : Type u} [Preorder D] {X : OrderedDomain.{u}}
    (hX : Figure11XDiagram X)
    (U₁ U₂ : ScottOpenCarrier
      ({ carrier := D, preorder := inferInstance } : OrderedDomain))
    {x : D} (hxI : x ∉ (ScottOpenCarrier.inter
      ({ carrier := D, preorder := inferInstance } : OrderedDomain) U₁ U₂).carrierSet) :
    Figure11PairContFun hX 3 (Or.inl rfl) U₁ U₂ x ≤ hX.point 4 := by
  by_cases hx₁ : x ∈ U₁.carrierSet <;>
    by_cases hx₂ : x ∈ U₂.carrierSet
  · exact False.elim (hxI ⟨hx₁, hx₂⟩)
  · simpa [Figure11PairContFun, Figure11PairFunction, hx₁, hx₂] using
      hX.left_le_joint (j := (4 : Fin 6)) (Or.inr (Or.inl rfl))
  · simpa [Figure11PairContFun, Figure11PairFunction, hx₁, hx₂] using
      hX.right_le_joint (j := (4 : Fin 6)) (Or.inr (Or.inl rfl))
  · simpa [Figure11PairContFun, Figure11PairFunction, hx₁, hx₂] using
      hX.bottom_le (hX.point 4)

theorem figure11CoverFunction_monotone
    {D : Type u} [Preorder D] {X : OrderedDomain.{u}}
    (hX : Figure11XDiagram X) (g : Chapter3.ContFun D X.carrier)
    (U₁ U₂ V : ScottOpenCarrier
      ({ carrier := D, preorder := inferInstance } : OrderedDomain))
    (hg : g ≤ Figure11PairContFun hX 3 (Or.inl rfl) U₁ U₂) :
    Monotone (Figure11CoverFunction hX g
      (ScottOpenCarrier.inter
        ({ carrier := D, preorder := inferInstance } : OrderedDomain) U₁ U₂) V) := by
  classical
  let I := ScottOpenCarrier.inter
    ({ carrier := D, preorder := inferInstance } : OrderedDomain) U₁ U₂
  intro x y hxy
  by_cases hxI : x ∈ I.carrierSet
  · have hyI : y ∈ I.carrierSet := Chapter2.scottOpen_upper I.scott_open hxI hxy
    by_cases hxV : x ∈ V.carrierSet
    · have hyV : y ∈ V.carrierSet := Chapter2.scottOpen_upper V.scott_open hxV hxy
      simp [Figure11CoverFunction, I, hxI, hyI, hxV, hyV]
    · by_cases hyV : y ∈ V.carrierSet
      · simpa [Figure11CoverFunction, I, hxI, hyI, hxV, hyV] using hX.c₂_le_top
      · simp [Figure11CoverFunction, I, hxI, hyI, hxV, hyV]
  · by_cases hyI : y ∈ I.carrierSet
    · have hgxc₂ : g x ≤ hX.point 4 :=
        le_trans (hg x) (figure11Pair_c₁_le_c₂_outside_inter hX U₁ U₂ hxI)
      by_cases hyV : y ∈ V.carrierSet
      · simpa [Figure11CoverFunction, I, hxI, hyI, hyV] using
          le_trans hgxc₂ hX.c₂_le_top
      · simpa [Figure11CoverFunction, I, hxI, hyI, hyV] using hgxc₂
    · simpa [Figure11CoverFunction, I, hxI, hyI] using g.continuous.1 hxy

theorem figure11CoverFunction_scottContinuous
    {D : Type u} [Preorder D] {X : OrderedDomain.{u}}
    (hX : Figure11XDiagram X) (g : Chapter3.ContFun D X.carrier)
    (U₁ U₂ V : ScottOpenCarrier
      ({ carrier := D, preorder := inferInstance } : OrderedDomain))
    (hg : g ≤ Figure11PairContFun hX 3 (Or.inl rfl) U₁ U₂) :
    Chapter3.ScottContinuous (Figure11CoverFunction hX g
      (ScottOpenCarrier.inter
        ({ carrier := D, preorder := inferInstance } : OrderedDomain) U₁ U₂) V) := by
  classical
  let I := ScottOpenCarrier.inter
    ({ carrier := D, preorder := inferInstance } : OrderedDomain) U₁ U₂
  constructor
  · exact figure11CoverFunction_monotone hX g U₁ U₂ V hg
  · intro A s hA hs
    constructor
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact figure11CoverFunction_monotone hX g U₁ U₂ V hg (hs.1 hx)
    · intro y hy
      by_cases hsI : s ∈ I.carrierSet
      · by_cases hsV : s ∈ V.carrierSet
        · rcases exists_mem_of_sup_mem_scottOpen hA hs I hsI with
            ⟨xI, hxIA, hxII⟩
          rcases exists_mem_of_sup_mem_scottOpen hA hs V hsV with
            ⟨xV, hxVA, hxVV⟩
          rcases hA.2 hxIA hxVA with ⟨x, hxA, hxIx, hxVx⟩
          have hxI := Chapter2.scottOpen_upper I.scott_open hxII hxIx
          have hxV := Chapter2.scottOpen_upper V.scott_open hxVV hxVx
          simpa [Figure11CoverFunction, I, hsI, hsV, hxI, hxV] using
            hy ⟨x, hxA, rfl⟩
        · rcases exists_mem_of_sup_mem_scottOpen hA hs I hsI with
            ⟨x, hxA, hxI⟩
          have hxNotV : x ∉ V.carrierSet := by
            intro hxV
            exact hsV (Chapter2.scottOpen_upper V.scott_open hxV (hs.1 hxA))
          simpa [Figure11CoverFunction, I, hsI, hsV, hxI, hxNotV] using
            hy ⟨x, hxA, rfl⟩
      · have hAoutside : ∀ x ∈ A, x ∉ I.carrierSet := by
          intro x hxA hxI
          exact hsI (Chapter2.scottOpen_upper I.scott_open hxI (hs.1 hxA))
        have hgSup := g.continuous.2 hA hs
        simp only [Figure11CoverFunction, I, hsI]
        exact hgSup.2 y (by
          intro z hz
          rcases hz with ⟨x, hxA, rfl⟩
          simpa [Figure11CoverFunction, I, hsI, hAoutside x hxA] using
            hy ⟨x, hxA, rfl⟩)

noncomputable def Figure11CoverContFun
    {D : Type u} [Preorder D] {X : OrderedDomain.{u}}
    (hX : Figure11XDiagram X) (g : Chapter3.ContFun D X.carrier)
    (U₁ U₂ V : ScottOpenCarrier
      ({ carrier := D, preorder := inferInstance } : OrderedDomain))
    (hg : g ≤ Figure11PairContFun hX 3 (Or.inl rfl) U₁ U₂) :
    Chapter3.ContFun D X.carrier where
  toFun := Figure11CoverFunction hX g
    (ScottOpenCarrier.inter
      ({ carrier := D, preorder := inferInstance } : OrderedDomain) U₁ U₂) V
  continuous := figure11CoverFunction_scottContinuous hX g U₁ U₂ V hg

theorem figure11CoverContFun_mono_cover
    {D : Type u} [Preorder D] {X : OrderedDomain.{u}}
    (hX : Figure11XDiagram X) (g : Chapter3.ContFun D X.carrier)
    (U₁ U₂ V W : ScottOpenCarrier
      ({ carrier := D, preorder := inferInstance } : OrderedDomain))
    (hg : g ≤ Figure11PairContFun hX 3 (Or.inl rfl) U₁ U₂)
    (hVW : V ≤ W) :
    Figure11CoverContFun hX g U₁ U₂ V hg ≤
      Figure11CoverContFun hX g U₁ U₂ W hg := by
  intro x
  let I := ScottOpenCarrier.inter
    ({ carrier := D, preorder := inferInstance } : OrderedDomain) U₁ U₂
  by_cases hxI : x ∈ I.carrierSet
  · by_cases hxV : x ∈ V.carrierSet
    · have hxW : x ∈ W.carrierSet := hVW hxV
      simp [Figure11CoverContFun, Figure11CoverFunction, I, hxI, hxV, hxW]
    · by_cases hxW : x ∈ W.carrierSet
      · simpa [Figure11CoverContFun, Figure11CoverFunction, I, hxI, hxV, hxW] using
          hX.c₂_le_top
      · simp [Figure11CoverContFun, Figure11CoverFunction, I, hxI, hxV, hxW]
  · simp [Figure11CoverContFun, Figure11CoverFunction, I, hxI]

/-- Corrected source Case 2: if `D` is noncoherent, the continuous-function
space from `D` to Figure 11's `X` cannot be continuous.

The printed proof uses one symbol `f` for two distinct maps and also leaves the
family equal to `g` outside the intersection.  Here `f_c₁` controls the common
approximant, `f_top` is the family supremum, and family members agree with
`f_c₁` outside the intersection.  This is the minimal pointwise repair that
makes all continuity, directedness, and supremum claims simultaneously true. -/
theorem not_continuous_functionSpace_of_figure11
    (D X : OrderedDomain.{u}) (hD : IsContinuousDomainObject D)
    (hNotCoherent : ¬ IsCoherentDomain D)
    (hX : Figure11XDiagram X) (hXdcpo : Chapter3.IsDcpo X.carrier) :
    ¬ Chapter3.IsContinuousDomain (Chapter3.ContFun D.carrier X.carrier) := by
  classical
  rcases exists_scottOpen_noncoherence_witness D hD hNotCoherent with
    ⟨O, U₁, U₂, hOU₁, hOU₂, hNotInter⟩
  let I := ScottOpenCarrier.inter D U₁ U₂
  rcases exists_directed_open_family_not_covering D hNotInter with
    ⟨A, sOpen, hA, hsOpen, hIsOpen, hNoCover⟩
  let f_c₁ : Chapter3.ContFun D.carrier X.carrier :=
    Figure11PairContFun hX 3 (Or.inl rfl) U₁ U₂
  let f_top : Chapter3.ContFun D.carrier X.carrier :=
    Figure11PairContFun hX 5 (Or.inr (Or.inr rfl)) U₁ U₂
  let f₁ : Chapter3.ContFun D.carrier X.carrier :=
    Figure11OpenStepContFun hX O 1
  let f₂ : Chapter3.ContFun D.carrier X.carrier :=
    Figure11OpenStepContFun hX O 2
  have hf₁ : f₁ ≪ f_c₁ := by
    exact openStep_left_le_figure11Pair hX hXdcpo O U₁ U₂ hOU₁
  have hf₂ : f₂ ≪ f_c₁ := by
    exact openStep_right_le_figure11Pair hX hXdcpo O U₁ U₂ hOU₂
  intro hContinuous
  rcases hContinuous with ⟨B, hBasis⟩
  have hApproxDir : Chapter3.DirectedSet (Chapter2.Approximants B f_c₁) :=
    (hBasis f_c₁).1
  have hApproxSup : Chapter3.IsSup (Chapter2.Approximants B f_c₁) f_c₁ :=
    (hBasis f_c₁).2
  rcases hf₁ hApproxDir hApproxSup le_rfl with ⟨g₁, hg₁, hf₁g₁⟩
  rcases hf₂ hApproxDir hApproxSup le_rfl with ⟨g₂, hg₂, hf₂g₂⟩
  rcases hApproxDir.2 hg₁ hg₂ with ⟨g, hg, hg₁g, hg₂g⟩
  have hf₁g : f₁ ≤ g := le_trans hf₁g₁ hg₁g
  have hf₂g : f₂ ≤ g := le_trans hf₂g₂ hg₂g
  have hg_c₁ : g ≪ f_c₁ := hg.2
  have hg_le_c₁ : g ≤ f_c₁ := Chapter3.wayBelow_le hg_c₁
  have hc₁top : f_c₁ ≤ f_top := figure11Pair_c₁_le_top hX U₁ U₂
  have hg_top : g ≪ f_top :=
    Chapter3.wayBelow_mono le_rfl hg_c₁ hc₁top
  let cover : ScottOpenCarrier D → Chapter3.ContFun D.carrier X.carrier :=
    fun V => Figure11CoverContFun hX f_c₁ U₁ U₂ V le_rfl
  have hCoverMonotone : Monotone cover := by
    intro V W hVW
    exact figure11CoverContFun_mono_cover hX f_c₁ U₁ U₂ V W le_rfl hVW
  have hCoverDirected : Chapter3.DirectedSet (cover '' A) :=
    Chapter2.DirectedSet.image hCoverMonotone hA
  let unionA : ScottOpenCarrier D :=
    { carrierSet := ⋃ V : A, V.1.carrierSet
      scott_open := Chapter2.scottOpen_iUnion (fun V : A => V.1.scott_open) }
  have hUnionSup : Chapter3.IsSup A unionA := by
    constructor
    · intro V hVA x hx
      change x ∈ ⋃ W : A, W.1.carrierSet
      rw [Set.mem_iUnion]
      exact ⟨⟨V, hVA⟩, hx⟩
    · intro V hV x hx
      change x ∈ ⋃ W : A, W.1.carrierSet at hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨W, hxW⟩
      exact hV W.2 hxW
  have hInterUnion : I ≤ unionA :=
    le_trans hIsOpen (hsOpen.2 unionA hUnionSup.1)
  have hCoverSup : Chapter3.IsSup (cover '' A) f_top := by
    constructor
    · intro h hh x
      rcases hh with ⟨V, hVA, rfl⟩
      by_cases hxI : x ∈ I.carrierSet
      · change x ∈ U₁.carrierSet ∩ U₂.carrierSet at hxI
        have hxI' : x ∈ (ScottOpenCarrier.inter
            ({ carrier := D.carrier, preorder := inferInstance } : OrderedDomain)
            U₁ U₂).carrierSet := ⟨hxI.1, hxI.2⟩
        by_cases hxV : x ∈ V.carrierSet
        · simp [cover, f_top, Figure11CoverContFun, Figure11CoverFunction,
            Figure11PairContFun, Figure11PairFunction, hxI.1, hxI.2, hxI', hxV]
        · simpa [cover, f_top, Figure11CoverContFun, Figure11CoverFunction,
            Figure11PairContFun, Figure11PairFunction, hxI.1, hxI.2, hxI', hxV] using
            hX.c₂_le_top
      · have hOutside : f_c₁ x = f_top x := by
          change ¬ (x ∈ U₁.carrierSet ∧ x ∈ U₂.carrierSet) at hxI
          rcases not_and_or.mp hxI with hx₁ | hx₂
          · simp [f_c₁, f_top, Figure11PairContFun, Figure11PairFunction, hx₁]
          · simp [f_c₁, f_top, Figure11PairContFun, Figure11PairFunction, hx₂]
        change ¬ (x ∈ U₁.carrierSet ∧ x ∈ U₂.carrierSet) at hxI
        have hxI' : x ∉ (ScottOpenCarrier.inter
            ({ carrier := D.carrier, preorder := inferInstance } : OrderedDomain)
            U₁ U₂).carrierSet := by
          intro hmem
          exact hxI ⟨hmem.1, hmem.2⟩
        simp [cover, Figure11CoverContFun, Figure11CoverFunction, hxI', hOutside]
    · intro y hy x
      by_cases hxI : x ∈ I.carrierSet
      · have hxUnion : x ∈ unionA.carrierSet := hInterUnion hxI
        change x ∈ U₁.carrierSet ∩ U₂.carrierSet at hxI
        have hxI' : x ∈ (ScottOpenCarrier.inter
            ({ carrier := D.carrier, preorder := inferInstance } : OrderedDomain)
            U₁ U₂).carrierSet := ⟨hxI.1, hxI.2⟩
        change x ∈ ⋃ W : A, W.1.carrierSet at hxUnion
        rw [Set.mem_iUnion] at hxUnion
        rcases hxUnion with ⟨V, hxV⟩
        have hAt := hy ⟨V.1, V.2, rfl⟩ x
        simpa [cover, f_top, Figure11CoverContFun, Figure11CoverFunction,
          Figure11PairContFun, Figure11PairFunction, hxI.1, hxI.2, hxI', hxV] using hAt
      · rcases hA.1 with ⟨V, hVA⟩
        have hAt := hy ⟨V, hVA, rfl⟩ x
        have hOutside : f_c₁ x = f_top x := by
          change ¬ (x ∈ U₁.carrierSet ∧ x ∈ U₂.carrierSet) at hxI
          rcases not_and_or.mp hxI with hx₁ | hx₂
          · simp [f_c₁, f_top, Figure11PairContFun, Figure11PairFunction, hx₁]
          · simp [f_c₁, f_top, Figure11PairContFun, Figure11PairFunction, hx₂]
        change ¬ (x ∈ U₁.carrierSet ∧ x ∈ U₂.carrierSet) at hxI
        have hxI' : x ∉ (ScottOpenCarrier.inter
            ({ carrier := D.carrier, preorder := inferInstance } : OrderedDomain)
            U₁ U₂).carrierSet := by
          intro hmem
          exact hxI ⟨hmem.1, hmem.2⟩
        simpa [cover, Figure11CoverContFun, Figure11CoverFunction, hxI',
          hOutside] using hAt
  have hNoCoverAbove : ∀ V ∈ A, ¬ g ≤ cover V := by
    intro V hVA hgV
    rcases Set.not_subset.mp (hNoCover V hVA) with ⟨x, hxO, hxNotV⟩
    have hxU₁ : x ∈ U₁.carrierSet := Chapter3.wayBelow_le hOU₁ hxO
    have hxU₂ : x ∈ U₂.carrierSet := Chapter3.wayBelow_le hOU₂ hxO
    have hleft : hX.point 1 ≤ g x := by
      simpa [f₁, Figure11OpenStepContFun, OpenStepContFun, OpenStepFunction, hxO] using
        hf₁g x
    have hright : hX.point 2 ≤ g x := by
      simpa [f₂, Figure11OpenStepContFun, OpenStepContFun, OpenStepFunction, hxO] using
        hf₂g x
    have hgc₁ : g x ≤ hX.point 3 := by
      simpa [f_c₁, Figure11PairContFun, Figure11PairFunction, hxU₁, hxU₂] using
        hg_le_c₁ x
    have hgEq : g x = hX.point 3 :=
      hX.eq_c₁_of_left_right_le_of_le_c₁ hleft hright hgc₁
    have hbad : hX.point 3 ≤ hX.point 4 := by
      have hxI' : x ∈ (ScottOpenCarrier.inter
          ({ carrier := D.carrier, preorder := inferInstance } : OrderedDomain)
          U₁ U₂).carrierSet := ⟨hxU₁, hxU₂⟩
      simpa [cover, Figure11CoverContFun, Figure11CoverFunction, hxI', hxU₁, hxU₂,
        hxNotV, hgEq] using hgV x
    exact hX.not_c₁_le_c₂ hbad
  rcases hg_top hCoverDirected hCoverSup le_rfl with ⟨h, hh, hgh⟩
  rcases hh with ⟨V, hVA, rfl⟩
  exact hNoCoverAbove V hVA hgh

end Chapter4
end AbramskyJung

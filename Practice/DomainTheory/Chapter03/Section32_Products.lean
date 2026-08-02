import Practice.DomainTheory.Chapter03.Prelude

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 3.2: products

This file contains the product constructions from Section 3.2, split out from
the chapter-level aggregator.
-/

universe u v w

namespace AbramskyJung
namespace Chapter3

section Products

variable {D : Type u} [Preorder D]
variable {E : Type v} [Preorder E]
variable {F : Type w} [Preorder F]

/-- Definition 3.2.1: cartesian product, Lean's product type. -/
abbrev CartesianProduct (D : Type u) (E : Type v) := D × E

/-- Proposition 3.2.2 partial clause: projected suprema assemble into a
coordinatewise supremum of a subset of a product. -/
theorem prod_isSup_of_projection_isSup {A : Set (D × E)} {dx : D} {ey : E}
    (hd : IsSup (Prod.fst '' A) dx) (he : IsSup (Prod.snd '' A) ey) :
    IsSup A (dx, ey) := by
  constructor
  · intro p hp
    constructor
    · exact hd.1 ⟨p, hp, rfl⟩
    · exact he.1 ⟨p, hp, rfl⟩
  · intro z hz
    constructor
    · exact hd.2 z.1 (by
        intro x hx
        rcases hx with ⟨p, hp, rfl⟩
        exact (hz hp).1)
    · exact he.2 z.2 (by
        intro y hy
        rcases hy with ⟨p, hp, rfl⟩
        exact (hz hp).2)

/-- Proposition 3.2.2, infimum clause: projected infima assemble into a
coordinatewise infimum of a subset of a product. -/
theorem prod_isInf_of_projection_isInf {A : Set (D × E)} {dx : D} {ey : E}
    (hd : IsInf (Prod.fst '' A) dx) (he : IsInf (Prod.snd '' A) ey) :
    IsInf A (dx, ey) := by
  constructor
  · intro p hp
    constructor
    · exact hd.1 ⟨p, hp, rfl⟩
    · exact he.1 ⟨p, hp, rfl⟩
  · intro z hz
    constructor
    · exact hd.2 z.1 (by
        intro x hx
        rcases hx with ⟨p, hp, rfl⟩
        exact (hz hp).1)
    · exact he.2 z.2 (by
        intro y hy
        rcases hy with ⟨p, hp, rfl⟩
        exact (hz hp).2)

/-- Product projection: first coordinate is Scott-continuous. -/
theorem prod_fst_scottContinuous : ScottContinuous (fun p : D × E => p.1) := by
  constructor
  · intro x y hxy
    exact hxy.1
  · intro A s hA hs
    constructor
    · intro x hx
      rcases hx with ⟨p, hp, rfl⟩
      exact (hs.1 hp).1
    · intro z hz
      exact (hs.2 (z, s.2) (by
        intro p hp
        exact ⟨hz ⟨p, hp, rfl⟩, (hs.1 hp).2⟩)).1

/-- Product projection: second coordinate is Scott-continuous. -/
theorem prod_snd_scottContinuous : ScottContinuous (fun p : D × E => p.2) := by
  constructor
  · intro x y hxy
    exact hxy.2
  · intro A s hA hs
    constructor
    · intro y hy
      rcases hy with ⟨p, hp, rfl⟩
      exact (hs.1 hp).2
    · intro z hz
      exact (hs.2 (s.1, z) (by
        intro p hp
        exact ⟨(hs.1 hp).1, hz ⟨p, hp, rfl⟩⟩)).2

/-- Proposition 3.2.3: pairing of Scott-continuous maps is Scott-continuous. -/
theorem prod_pair_scottContinuous {f : F → D} {g : F → E}
    (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous (fun x : F => (f x, g x)) := by
  constructor
  · intro x y hxy
    exact ⟨hf.1 hxy, hg.1 hxy⟩
  · intro A s hA hs
    apply prod_isSup_of_projection_isSup
    · have hfs : IsSup (f '' A) (f s) := hf.2 hA hs
      have hEq : Prod.fst '' ((fun x : F => (f x, g x)) '' A) = f '' A := by
        ext z
        constructor
        · intro hz
          rcases hz with ⟨p, hp, rfl⟩
          rcases hp with ⟨a, ha, rfl⟩
          exact ⟨a, ha, rfl⟩
        · intro hz
          rcases hz with ⟨a, ha, rfl⟩
          exact ⟨(f a, g a), ⟨a, ha, rfl⟩, rfl⟩
      simpa [hEq] using hfs
    · have hgs : IsSup (g '' A) (g s) := hg.2 hA hs
      have hEq : Prod.snd '' ((fun x : F => (f x, g x)) '' A) = g '' A := by
        ext z
        constructor
        · intro hz
          rcases hz with ⟨p, hp, rfl⟩
          rcases hp with ⟨a, ha, rfl⟩
          exact ⟨a, ha, rfl⟩
        · intro hz
          rcases hz with ⟨a, ha, rfl⟩
          exact ⟨(f a, g a), ⟨a, ha, rfl⟩, rfl⟩
      simpa [hEq] using hgs

/-- Proposition 3.2.3: if `f` and `g` are Scott-continuous, then so is the
product map `f × g`. -/
theorem prod_map_scottContinuous
    {D' : Type u} {E' : Type v} [Preorder D'] [Preorder E']
    {f : D → D'} {g : E → E'}
    (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous (fun p : D × E => (f p.1, g p.2)) := by
  exact prod_pair_scottContinuous
    (ScottContinuous.comp hf prod_fst_scottContinuous)
    (ScottContinuous.comp hg prod_snd_scottContinuous)

/-- Constant maps are Scott-continuous. -/
theorem const_scottContinuous (e : E) : ScottContinuous (fun _ : D => e) := by
  constructor
  · intro _ _
    exact fun _ => le_rfl
  · intro A _ hA _
    have hEq : (fun _ : D => e) '' A = ({e} : Set E) := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨_, _, rfl⟩
        simp
      · intro hy
        have hye : y = e := by simpa using hy
        rcases hA.1 with ⟨a, ha⟩
        exact ⟨a, ha, hye.symm⟩
    simpa [hEq] using Chapter2.isSup_singleton e

/-- The left product section `d ↦ (d,e)` is Scott-continuous. -/
theorem prod_left_section_scottContinuous (e : E) :
    ScottContinuous (fun d : D => (d, e)) := by
  exact prod_pair_scottContinuous scottContinuous_id (const_scottContinuous e)

/-- The right product section `e ↦ (d,e)` is Scott-continuous. -/
theorem prod_right_section_scottContinuous (d : D) :
    ScottContinuous (fun e : E => (d, e)) := by
  exact prod_pair_scottContinuous (const_scottContinuous d) scottContinuous_id

/-- A product set is directed if both factors are directed. -/
theorem directed_prod {A : Set D} {B : Set E}
    (hA : DirectedSet A) (hB : DirectedSet B) :
    DirectedSet ({p : D × E | p.1 ∈ A ∧ p.2 ∈ B} : Set (D × E)) := by
  constructor
  · rcases hA.1 with ⟨a, ha⟩
    rcases hB.1 with ⟨b, hb⟩
    exact ⟨(a, b), ⟨ha, hb⟩⟩
  · intro x hx y hy
    rcases hA.2 hx.1 hy.1 with ⟨a, ha, hxa, hya⟩
    rcases hB.2 hx.2 hy.2 with ⟨b, hb, hxb, hyb⟩
    exact ⟨(a, b), ⟨ha, hb⟩, ⟨hxa, hxb⟩, ⟨hya, hyb⟩⟩

/-- From a supremum in a product, first coordinate is a supremum of first projections. -/
theorem prod_fst_isSup {A : Set (D × E)} {s : D × E} (hs : IsSup A s) :
    IsSup (Prod.fst '' A) s.1 := by
  constructor
  · intro x hx
    rcases hx with ⟨p, hp, rfl⟩
    exact (hs.1 hp).1
  · intro z hz
    exact (hs.2 (z, s.2) (by
      intro p hp
      exact ⟨hz ⟨p, hp, rfl⟩, (hs.1 hp).2⟩)).1

/-- From a supremum in a product, second coordinate is a supremum of second projections. -/
theorem prod_snd_isSup {A : Set (D × E)} {s : D × E} (hs : IsSup A s) :
    IsSup (Prod.snd '' A) s.2 := by
  constructor
  · intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    exact (hs.1 hp).2
  · intro z hz
    exact (hs.2 (s.1, z) (by
      intro p hp
      exact ⟨(hs.1 hp).1, hz ⟨p, hp, rfl⟩⟩)).2

/-- From an infimum in a product, first coordinate is an infimum of first projections. -/
theorem prod_fst_isInf {A : Set (D × E)} {s : D × E} (hs : IsInf A s) :
    IsInf (Prod.fst '' A) s.1 := by
  constructor
  · intro x hx
    rcases hx with ⟨p, hp, rfl⟩
    exact (hs.1 hp).1
  · intro z hz
    exact (hs.2 (z, s.2) (by
      intro p hp
      exact ⟨hz ⟨p, hp, rfl⟩, (hs.1 hp).2⟩)).1

/-- From an infimum in a product, second coordinate is an infimum of second projections. -/
theorem prod_snd_isInf {A : Set (D × E)} {s : D × E} (hs : IsInf A s) :
    IsInf (Prod.snd '' A) s.2 := by
  constructor
  · intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    exact (hs.1 hp).2
  · intro z hz
    exact (hs.2 (s.1, z) (by
      intro p hp
      exact ⟨(hs.1 hp).1, hz ⟨p, hp, rfl⟩⟩)).2

/-- Proposition 3.2.2: the cartesian product of dcpos is a dcpo, with directed
suprema computed coordinatewise. -/
theorem prod_isDcpo (hD : IsDcpo D) (hE : IsDcpo E) : IsDcpo (D × E) := by
  intro A hA
  have hfstDir : DirectedSet (Prod.fst '' A) :=
    DirectedSet.image (f := fun p : D × E => p.1) (by
      intro p q hpq
      exact hpq.1) hA
  have hsndDir : DirectedSet (Prod.snd '' A) :=
    DirectedSet.image (f := fun p : D × E => p.2) (by
      intro p q hpq
      exact hpq.2) hA
  rcases hD (Prod.fst '' A) hfstDir with ⟨dx, hdx⟩
  rcases hE (Prod.snd '' A) hsndDir with ⟨ey, hey⟩
  exact ⟨(dx, ey), prod_isSup_of_projection_isSup hdx hey⟩

/-- Proposition 3.2.4(1): way-below in products is coordinatewise. -/
theorem prod_wayBelow_iff {x x' : D} {y y' : E} :
    WayBelow ((x, y) : D × E) (x', y') ↔ WayBelow x x' ∧ WayBelow y y' := by
  constructor
  · intro h
    constructor
    · intro A s hA hs hx's
      have hB : DirectedSet ({p : D × E | p.1 ∈ A ∧ p.2 = y'} : Set (D × E)) := by
        constructor
        · rcases hA.1 with ⟨a, ha⟩
          exact ⟨(a, y'), ⟨ha, rfl⟩⟩
        · intro p hp q hq
          rcases hA.2 hp.1 hq.1 with ⟨a, ha, hpa, hqa⟩
          exact ⟨(a, y'), ⟨ha, rfl⟩, ⟨hpa, by simp [hp.2]⟩, ⟨hqa, by simp [hq.2]⟩⟩
      have hsupB : IsSup ({p : D × E | p.1 ∈ A ∧ p.2 = y'} : Set (D × E)) (s, y') := by
        apply prod_isSup_of_projection_isSup
        · have hEq : Prod.fst '' ({p : D × E | p.1 ∈ A ∧ p.2 = y'} : Set (D × E)) = A := by
            ext z
            constructor
            · intro hz
              rcases hz with ⟨p, hp, rfl⟩
              exact hp.1
            · intro hz
              exact ⟨(z, y'), ⟨hz, rfl⟩, rfl⟩
          simpa [hEq] using hs
        · have hEq : Prod.snd '' ({p : D × E | p.1 ∈ A ∧ p.2 = y'} : Set (D × E)) = ({y'} : Set E) := by
            ext z
            constructor
            · intro hz
              rcases hz with ⟨p, hp, rfl⟩
              simp [hp.2]
            · intro hz
              have hz' : z = y' := by simpa using hz
              subst z
              rcases hA.1 with ⟨a, ha⟩
              exact ⟨(a, y'), ⟨ha, rfl⟩, rfl⟩
          have hsingle : IsSup ({y'} : Set E) y' := by
            constructor
            · intro a ha
              have hay : a = y' := by simpa using ha
              simpa [hay]
            · intro z hz
              exact hz (a := y') (by simp)
          simpa [hEq] using hsingle
      rcases h hB hsupB ⟨hx's, le_rfl⟩ with ⟨p, hp, hxp⟩
      exact ⟨p.1, hp.1, hxp.1⟩
    · intro A s hA hs hy's
      have hB : DirectedSet ({p : D × E | p.1 = x' ∧ p.2 ∈ A} : Set (D × E)) := by
        constructor
        · rcases hA.1 with ⟨a, ha⟩
          exact ⟨(x', a), ⟨rfl, ha⟩⟩
        · intro p hp q hq
          rcases hA.2 hp.2 hq.2 with ⟨a, ha, hpa, hqa⟩
          exact ⟨(x', a), ⟨rfl, ha⟩, ⟨by simp [hp.1], hpa⟩, ⟨by simp [hq.1], hqa⟩⟩
      have hsupB : IsSup ({p : D × E | p.1 = x' ∧ p.2 ∈ A} : Set (D × E)) (x', s) := by
        apply prod_isSup_of_projection_isSup
        · have hEq : Prod.fst '' ({p : D × E | p.1 = x' ∧ p.2 ∈ A} : Set (D × E)) = ({x'} : Set D) := by
            ext z
            constructor
            · intro hz
              rcases hz with ⟨p, hp, rfl⟩
              simp [hp.1]
            · intro hz
              have hz' : z = x' := by simpa using hz
              subst z
              rcases hA.1 with ⟨a, ha⟩
              exact ⟨(x', a), ⟨rfl, ha⟩, rfl⟩
          have hsingle : IsSup ({x'} : Set D) x' := by
            constructor
            · intro a ha
              have hax : a = x' := by simpa using ha
              simpa [hax]
            · intro z hz
              exact hz (a := x') (by simp)
          simpa [hEq] using hsingle
        · have hEq : Prod.snd '' ({p : D × E | p.1 = x' ∧ p.2 ∈ A} : Set (D × E)) = A := by
            ext z
            constructor
            · intro hz
              rcases hz with ⟨p, hp, rfl⟩
              exact hp.2
            · intro hz
              exact ⟨(x', z), ⟨rfl, hz⟩, rfl⟩
          simpa [hEq] using hs
      rcases h hB hsupB ⟨le_rfl, hy's⟩ with ⟨p, hp, hyp⟩
      exact ⟨p.2, hp.2, hyp.2⟩
  · intro hxy
    rcases hxy with ⟨hx, hy⟩
    intro A s hA hs hpairs
    have hfstSup : IsSup (Prod.fst '' A) s.1 := prod_fst_isSup hs
    have hsndSup : IsSup (Prod.snd '' A) s.2 := prod_snd_isSup hs
    rcases hx (DirectedSet.image (f := fun p : D × E => p.1) (by intro p q hpq; exact hpq.1) hA) hfstSup hpairs.1 with ⟨a1, ha1, hxa1⟩
    rcases hy (DirectedSet.image (f := fun p : D × E => p.2) (by intro p q hpq; exact hpq.2) hA) hsndSup hpairs.2 with ⟨a2, ha2, hya2⟩
    rcases ha1 with ⟨p1, hp1, rfl⟩
    rcases ha2 with ⟨p2, hp2, rfl⟩
    rcases hA.2 hp1 hp2 with ⟨p3, hp3, hp13, hp23⟩
    exact ⟨p3, hp3, le_trans hxa1 hp13.1, le_trans hya2 hp23.2⟩

/-- Product basis set. -/
def ProdBasis (B : Set D) (C : Set E) : Set (D × E) :=
  {p | p.1 ∈ B ∧ p.2 ∈ C}

/-- Proposition 3.2.4(2): product of bases is a basis. -/
theorem prod_basis {B : Set D} {C : Set E}
    (hB : IsBasis B) (hC : IsBasis C) : IsBasis (ProdBasis B C) := by
  intro p
  constructor
  · have hBD : DirectedSet (Approximants B p.1) := (hB p.1).1
    have hCE : DirectedSet (Approximants C p.2) := (hC p.2).1
    have hdir := directed_prod hBD hCE
    have hEq : Approximants (ProdBasis B C) p =
        ({q : D × E | q.1 ∈ Approximants B p.1 ∧ q.2 ∈ Approximants C p.2} : Set (D × E)) := by
      ext q
      constructor
      · intro hq
        rcases hq with ⟨hqBC, hqw⟩
        have hw := (prod_wayBelow_iff).1 hqw
        exact ⟨⟨hqBC.1, hw.1⟩, ⟨hqBC.2, hw.2⟩⟩
      · intro hq
        exact ⟨⟨hq.1.1, hq.2.1⟩, (prod_wayBelow_iff).2 ⟨hq.1.2, hq.2.2⟩⟩
    simpa [hEq] using hdir
  · have hBDsup : IsSup (Approximants B p.1) p.1 := (hB p.1).2
    have hCEsup : IsSup (Approximants C p.2) p.2 := (hC p.2).2
    have hprodSup : IsSup ({q : D × E | q.1 ∈ Approximants B p.1 ∧ q.2 ∈ Approximants C p.2} : Set (D × E)) p :=
      prod_isSup_of_projection_isSup (by
        have hEq : Prod.fst '' ({q : D × E | q.1 ∈ Approximants B p.1 ∧ q.2 ∈ Approximants C p.2} : Set (D × E)) = Approximants B p.1 := by
          ext z
          constructor
          · intro hz
            rcases hz with ⟨q, hq, rfl⟩
            exact hq.1
          · intro hz
            rcases (hC p.2).1.1 with ⟨c, hc⟩
            exact ⟨(z, c), ⟨hz, hc⟩, rfl⟩
        simpa [hEq] using hBDsup) (by
        have hEq : Prod.snd '' ({q : D × E | q.1 ∈ Approximants B p.1 ∧ q.2 ∈ Approximants C p.2} : Set (D × E)) = Approximants C p.2 := by
          ext z
          constructor
          · intro hz
            rcases hz with ⟨q, hq, rfl⟩
            exact hq.2
          · intro hz
            rcases (hB p.1).1.1 with ⟨b, hb⟩
            exact ⟨(b, z), ⟨hb, hz⟩, rfl⟩
        simpa [hEq] using hCEsup)
    have hEq : Approximants (ProdBasis B C) p =
        ({q : D × E | q.1 ∈ Approximants B p.1 ∧ q.2 ∈ Approximants C p.2} : Set (D × E)) := by
      ext q
      constructor
      · intro hq
        rcases hq with ⟨hqBC, hqw⟩
        have hw := (prod_wayBelow_iff).1 hqw
        exact ⟨⟨hqBC.1, hw.1⟩, ⟨hqBC.2, hw.2⟩⟩
      · intro hq
        exact ⟨⟨hq.1.1, hq.2.1⟩, (prod_wayBelow_iff).2 ⟨hq.1.2, hq.2.2⟩⟩
    simpa [hEq] using hprodSup

/-- Proposition 3.2.4(3): product of continuous domains is continuous. -/
theorem prod_continuous_domain
    (hD : IsContinuousDomain D) (hE : IsContinuousDomain E) :
    IsContinuousDomain (D × E) := by
  rcases hD with ⟨B, hB⟩
  rcases hE with ⟨C, hC⟩
  exact ⟨ProdBasis B C, prod_basis hB hC⟩

/-- Proposition 3.2.4(4): compactness in products is coordinatewise. -/
theorem prod_compact_iff {x : D} {y : E} :
    Compact ((x, y) : D × E) ↔ Compact x ∧ Compact y := by
  exact prod_wayBelow_iff

/-- Proposition 3.2.4(4): the compact elements of a product are the products of
compact elements. -/
theorem prod_compactSet_eq :
    (Chapter2.CompactSet : Set (D × E)) =
      ProdBasis (Chapter2.CompactSet : Set D) (Chapter2.CompactSet : Set E) := by
  ext p
  exact prod_compact_iff

/-- Products preserve algebraicity in the strong compact-basis presentation. -/
theorem prod_algebraic_domain
    (hD : IsAlgebraicDomain D) (hE : IsAlgebraicDomain E) :
    IsAlgebraicDomain (D × E) := by
  have hBasis :
      IsBasis (ProdBasis (Chapter2.CompactSet : Set D) (Chapter2.CompactSet : Set E)) :=
    prod_basis hD hE
  change IsBasis (Chapter2.CompactSet : Set (D × E))
  rw [prod_compactSet_eq]
  exact hBasis

end Products

end Chapter3
end AbramskyJung

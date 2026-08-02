import Practice.DomainTheory.Chapter03.Section31_EmbeddingProjection

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 3.3: expanding sequences
-/

universe u

namespace AbramskyJung
namespace Chapter3

section ExpandingSequences

/-- Definition 3.3.6. PDF text: "A diagram `⟨(D_n)_{n∈N},
(e_mn : D_n → D_m)_{n≤m∈N}⟩` in the category `DCPO` is called an expanding
sequence, if the following conditions are satisfied: (1) each `e_mn` is an
embedding, with associated projection denoted `p_nm`; (2) `e_nn = id_{D_n}`;
(3) for `n ≤ m ≤ k`, `e_kn = e_km ∘ e_mn`."  PDF note: because lower
adjoints determine upper adjoints and vice versa, `p_nk = p_nm ∘ p_mk`
whenever `n ≤ m ≤ k`.

Current Lean spelling: the stage carriers are preorder-indexed, while dcpo and
poset hypotheses are supplied by the theorems that need them.  The fields record
both the embedding maps and their associated projections as e-p-pairs, together
with the identity and composition laws for embeddings from the PDF. -/
structure ExpandingSequence (D : Nat → Type u) [inst : ∀ n : Nat, Preorder (D n)] where
  e : ∀ {n m : Nat}, n ≤ m → D n → D m
  p : ∀ {n m : Nat}, n ≤ m → D m → D n
  continuous_e : ∀ {n m : Nat} (h : n ≤ m), ScottContinuous (e h)
  continuous_p : ∀ {n m : Nat} (h : n ≤ m), ScottContinuous (p h)
  retract : ∀ {n m : Nat} (h : n ≤ m) (x : D n), p h (e h x) = x
  below : ∀ {n m : Nat} (h : n ≤ m) (y : D m), e h (p h y) ≤ y
  id_e : ∀ (n : Nat) (h : n ≤ n) (x : D n), e h x = x
  comp_e : ∀ {n m k : Nat} (hnm : n ≤ m) (hmk : m ≤ k) (hnk : n ≤ k) (x : D n),
    e hnk x = e hmk (e hnm x)

namespace ExpandingSequence

variable {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
variable (S : ExpandingSequence D)

/-- The e-p-pair at a fixed comparison `n ≤ m`. -/
def epPair {n m : Nat} (h : n ≤ m) : EPPair (D n) (D m) where
  e := S.e h
  p := S.p h
  continuous_e := S.continuous_e h
  continuous_p := S.continuous_p h
  retract := S.retract h
  below := S.below h

/-- The embedding and projection at `n ≤ m` form an adjunction inequality. -/
theorem e_le_iff_le_p {n m : Nat} (h : n ≤ m) (x : D n) (y : D m) :
    S.e h x ≤ y ↔ x ≤ S.p h y := by
  constructor
  · intro hle
    calc
      x = S.p h (S.e h x) := (S.retract h x).symm
      _ ≤ S.p h y := (S.continuous_p h).1 hle
  · intro hle
    calc
      S.e h x ≤ S.e h (S.p h y) := (S.continuous_e h).1 hle
      _ ≤ y := S.below h y

/-- Definition 3.3.6 note: the projection at `n ≤ n` is the identity. -/
theorem id_p (n : Nat) (h : n ≤ n) (x : D n) :
    S.p h x = x := by
  calc
    S.p h x = S.p h (S.e h x) := by rw [S.id_e n h x]
    _ = x := S.retract h x

/-- Definition 3.3.6 note. PDF note: associated projections compose in
the opposite direction, `p_{n,k} = p_{n,m} ∘ p_{m,k}`.

Current Lean spelling: because the local stages are preorders rather than
bundled posets, the equality uses explicit antisymmetry of the source stage,
matching the book's uniqueness argument for adjoints. -/
theorem comp_p_of_antisymm
    {n m k : Nat} (hnm : n ≤ m) (hmk : m ≤ k) (hnk : n ≤ k)
    (hanti : ∀ x y : D n, x ≤ y → y ≤ x → x = y) (x : D k) :
    S.p hnm (S.p hmk x) = S.p hnk x := by
  apply hanti
  · apply (S.e_le_iff_le_p hnk (S.p hnm (S.p hmk x)) x).1
    calc
      S.e hnk (S.p hnm (S.p hmk x))
          = S.e hmk (S.e hnm (S.p hnm (S.p hmk x))) :=
            S.comp_e hnm hmk hnk (S.p hnm (S.p hmk x))
      _ ≤ S.e hmk (S.p hmk x) :=
        (S.continuous_e hmk).1 (S.below hnm (S.p hmk x))
      _ ≤ x := S.below hmk x
  · apply (S.e_le_iff_le_p hnm (S.p hnk x) (S.p hmk x)).1
    apply (S.e_le_iff_le_p hmk (S.e hnm (S.p hnk x)) x).1
    calc
      S.e hmk (S.e hnm (S.p hnk x))
          = S.e hnk (S.p hnk x) :=
            (S.comp_e hnm hmk hnk (S.p hnk x)).symm
      _ ≤ x := S.below hnk x

end ExpandingSequence

/-- The carrier predicate of the limit object in Theorem 3.3.7. -/
def BilimitCarrier {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D) (x : ∀ n : Nat, D n) : Prop :=
  ∀ {n m : Nat} (h : n ≤ m), x n = S.p h (x m)

/-- The bundled carrier of the bilimit constructed in Theorem 3.3.7. -/
def Bilimit {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D) : Type u :=
  {x : ∀ n : Nat, D n // BilimitCarrier S x}

/-- Limiting projection from the bilimit to the `n`-th stage. -/
def Bilimit.proj {D : Nat → Type u} [∀ n : Nat, Preorder (D n)]
    (S : ExpandingSequence D) (n : Nat) : Bilimit S → D n :=
  fun x => x.1 n

end ExpandingSequences

end Chapter3
end AbramskyJung

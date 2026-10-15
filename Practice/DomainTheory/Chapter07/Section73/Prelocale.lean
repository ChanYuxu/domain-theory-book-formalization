import Practice.DomainTheory.Chapter06.Section62
import Practice.DomainTheory.Chapter07.Section72

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 7.3: prelocales and localic constructions

This module follows one coherent dependency cluster inside the textbook
section. The stable public import remains
`Practice.DomainTheory.Chapter07.Section73`.
-/

universe u v

namespace AbramskyJung
namespace Chapter7

def RelEquiv {α : Type u} (le : α → α → Prop) (x y : α) : Prop :=
  le x y ∧ le y x

/-- Finite joins in a prelocale term algebra. -/
def ListJoin {α : Type u} (sup : α → α → α) (zero : α) : List α → α
  | [] => zero
  | x :: xs => sup x (ListJoin sup zero xs)

/-- Finite meets in a prelocale term algebra. -/
def ListMeet {α : Type u} (inf : α → α → α) (one : α) : List α → α
  | [] => one
  | x :: xs => inf x (ListMeet inf one xs)

/-- Join-primality with respect to explicit prelocale operations, excluding the
least element up to preorder equivalence as in Definition 7.1.5. -/
def IsJoinPrimeRel {α : Type u} (le : α → α → Prop) (sup : α → α → α)
    (zero p : α) : Prop :=
  ¬ RelEquiv le p zero ∧
    ∀ a b : α, le p (sup a b) → le p a ∨ le p b

/-- Definition 7.3.1: coherent algebraic prelocales. -/
structure CoherentAlgebraicPrelocale where
  carrier : Type u
  le : carrier → carrier → Prop
  le_refl : ∀ a : carrier, le a a
  le_trans : ∀ ⦃a b c : carrier⦄, le a b → le b c → le a c
  sup : carrier → carrier → carrier
  inf : carrier → carrier → carrier
  zero : carrier
  one : carrier
  C : carrier → Prop
  sup_is_sup : ∀ a b c : carrier, le (sup a b) c ↔ le a c ∧ le b c
  inf_is_inf : ∀ a b c : carrier, le c (inf a b) ↔ le c a ∧ le c b
  zero_le : ∀ a : carrier, le zero a
  le_one : ∀ a : carrier, le a one
  C_iff_join_prime : ∀ a : carrier, C a ↔ IsJoinPrimeRel le sup zero a
  finite_prime_generation :
    ∀ a : carrier,
      ∃ l : List carrier,
        (∀ x : carrier, x ∈ l → C x) ∧ RelEquiv le (ListJoin sup zero l) a

namespace CoherentAlgebraicPrelocale

/-- The equivalence relation associated to a prelocale. -/
def Eqv (A : CoherentAlgebraicPrelocale.{u}) (a b : A.carrier) : Prop :=
  RelEquiv A.le a b

end CoherentAlgebraicPrelocale

/-- A lower-bound universal property for the finite meet of a subset in a
prelocale.  In `DomainPrelocale.finite_mub_closure` the subset is constrained
to lie inside a finite set of join-primes. -/
def IsFiniteMeetOfSet (A : CoherentAlgebraicPrelocale.{u})
    (W : Set A.carrier) (m : A.carrier) : Prop :=
  (∀ w : A.carrier, w ∈ W → A.le m w) ∧
    ∀ y : A.carrier, (∀ w : A.carrier, w ∈ W → A.le y w) → A.le y m

/-- An upper-bound universal property for the finite join of a subset in a
prelocale.  In `DomainPrelocale.finite_mub_closure` the subset is constrained
to lie inside a finite set of join-primes. -/
def IsFiniteJoinOfSet (A : CoherentAlgebraicPrelocale.{u})
    (Z : Set A.carrier) (j : A.carrier) : Prop :=
  (∀ z : A.carrier, z ∈ Z → A.le z j) ∧
    ∀ y : A.carrier, (∀ z : A.carrier, z ∈ Z → A.le z y) → A.le j y

/-- The finite meet of `W` is equivalent to the finite join of `Z`, matching the
`∧W = ∨Z` clause in Definition 7.3.1. -/
def FiniteMeetEqFiniteJoin (A : CoherentAlgebraicPrelocale.{u})
    (W Z : Set A.carrier) : Prop :=
  ∃ m j : A.carrier,
    IsFiniteMeetOfSet A W m ∧ IsFiniteJoinOfSet A Z j ∧ RelEquiv A.le m j

/-- Domain prelocales add a finite-mub witness shape and a prime top element.
The finite-mub field records the PDF clause
`∀ W ⊆ V, ∃ Z ⊆ V, inf W ≈ sup Z`. -/
structure DomainPrelocale extends CoherentAlgebraicPrelocale.{u} where
  finite_mub_closure :
    ∀ U : Set carrier, U.Finite → (∀ u ∈ U, C u) →
      ∃ V : Set carrier,
        V.Finite ∧ U ⊆ V ∧ (∀ v ∈ V, C v) ∧
          ∀ W : Set carrier, W ⊆ V →
            ∃ Z : Set carrier, Z ⊆ V ∧
              FiniteMeetEqFiniteJoin toCoherentAlgebraicPrelocale W Z
  top_prime : C one

/-- Definition 7.3.1, named book entry. -/
abbrev def_7_3_1_domain_prelocale :=
  DomainPrelocale.{u}

/-- Filters in a domain prelocale.  The properness clause excludes the
improper all-elements filter, matching the spectrum used in the localic
duality statements. -/
structure IsPrelocaleFilter (A : DomainPrelocale.{u}) (F : Set A.carrier) : Prop where
  one_mem : A.one ∈ F
  zero_not_mem : A.zero ∉ F
  upward_closed : ∀ ⦃a b : A.carrier⦄, a ∈ F → A.le a b → b ∈ F
  inf_closed : ∀ ⦃a b : A.carrier⦄, a ∈ F → b ∈ F → A.inf a b ∈ F

/-- Prime filters in a prelocale spectrum. -/
structure IsPrimePrelocaleFilter (A : DomainPrelocale.{u}) (F : Set A.carrier) :
    Prop extends IsPrelocaleFilter A F where
  sup_prime : ∀ a b : A.carrier, A.sup a b ∈ F → a ∈ F ∨ b ∈ F

/-- The spectrum of a domain prelocale. -/
def Spec (A : DomainPrelocale.{u}) : Type u :=
  {F : Set A.carrier // IsPrimePrelocaleFilter A F}

/-- Definition 7.3.2: pre-isomorphisms between domain prelocales. -/
structure PreIsomorphism (A B : DomainPrelocale.{u}) where
  toFun : A.carrier → B.carrier
  surjective : Function.Surjective toFun
  monotone : ∀ ⦃a b : A.carrier⦄, A.le a b → B.le (toFun a) (toFun b)
  order_reflecting : ∀ ⦃a b : A.carrier⦄, B.le (toFun a) (toFun b) → A.le a b
  sup_preserving :
    ∀ a b : A.carrier,
      RelEquiv B.le (toFun (A.sup a b)) (B.sup (toFun a) (toFun b))
  inf_preserving :
    ∀ a b : A.carrier,
      RelEquiv B.le (toFun (A.inf a b)) (B.inf (toFun a) (toFun b))
  zero_preserving : RelEquiv B.le (toFun A.zero) B.zero
  one_preserving : RelEquiv B.le (toFun A.one) B.one
  C_preserving : ∀ a : A.carrier, A.C a → B.C (toFun a)
  C_reflecting : ∀ a : A.carrier, B.C (toFun a) → A.C a
  C_surjective :
    ∀ b : B.carrier, B.C b →
      ∃ a : A.carrier, A.C a ∧ RelEquiv B.le (toFun a) b

/-- Scott compactness for subsets of an ordered domain, phrased using
Scott-open covers. -/
def ScottCompactSet (D : Chapter4.OrderedDomain.{u}) (K : Set D.carrier) : Prop :=
  ∀ cover : Set (Set D.carrier),
    (∀ U ∈ cover, @Chapter2.ScottOpen D.carrier D.preorder U) →
      K ⊆ ⋃₀ cover →
        ∃ finiteCover : Set (Set D.carrier),
          finiteCover.Finite ∧ finiteCover ⊆ cover ∧ K ⊆ ⋃₀ finiteCover

/-- Compact-open subsets of a domain: the carrier of the compact-open lattice
`KΩ(D)` used in Definition 7.3.2. -/
structure CompactOpenSet (D : Chapter4.OrderedDomain.{u}) where
  carrier : Set D.carrier
  scott_open : @Chapter2.ScottOpen D.carrier D.preorder carrier
  compact : ScottCompactSet D carrier

/-- Principal compact-open subsets `↑c`, the join-prime compact-opens
`C(KΩ(D))` appearing below Definition 7.3.2. -/
def IsPrincipalCompactOpen
    (D : Chapter4.OrderedDomain.{u}) (O : CompactOpenSet D) : Prop :=
  ∃ c : D.carrier,
    @Chapter2.Compact D.carrier D.preorder c ∧
      O.carrier = {x : D.carrier | c ≤ x}

/-- A localic description of a bifinite domain by a domain prelocale.  The
interpretation lands in compact-open subsets, matching the book's
pre-isomorphism `A → KΩ(D)` up to the current bundled interface. -/
structure LocalicDescription
    (A : DomainPrelocale.{u}) (D : Chapter4.BifiniteDomain.{u}) where
  interpret : A.carrier → CompactOpenSet D.object
  surjective : ∀ O : CompactOpenSet D.object, ∃ a : A.carrier,
    (interpret a).carrier = O.carrier
  order_preserving : ∀ ⦃a b : A.carrier⦄, A.le a b →
    (interpret a).carrier ⊆ (interpret b).carrier
  order_reflecting : ∀ ⦃a b : A.carrier⦄,
    (interpret a).carrier ⊆ (interpret b).carrier → A.le a b
  sup_preserving :
    ∀ a b : A.carrier,
      (interpret (A.sup a b)).carrier = (interpret a).carrier ∪ (interpret b).carrier
  inf_preserving :
    ∀ a b : A.carrier,
      (interpret (A.inf a b)).carrier = (interpret a).carrier ∩ (interpret b).carrier
  zero_preserving : (interpret A.zero).carrier = ∅
  one_preserving : (interpret A.one).carrier = Set.univ
  C_to_principal :
    ∀ a : A.carrier, A.C a → IsPrincipalCompactOpen D.object (interpret a)
  principal_surjective :
    ∀ O : CompactOpenSet D.object, IsPrincipalCompactOpen D.object O →
      ∃ a : A.carrier, A.C a ∧ (interpret a).carrier = O.carrier

/-- Definition 7.3.2: the two notions introduced in the PDF.  The named entry
records the type form of pre-isomorphisms and localic descriptions; it does not
assert that either structure exists for arbitrary inputs. -/
structure PreIsomorphismLocalicDescriptionNotions where
  pre_isomorphism : DomainPrelocale.{u} → DomainPrelocale.{u} → Type u
  localic_description : DomainPrelocale.{u} → Chapter4.BifiniteDomain.{u} → Type u

/-- Definition 7.3.2, named book entry. -/
def def_7_3_2_preisomorphism_localic_description :
    PreIsomorphismLocalicDescriptionNotions.{u} where
  pre_isomorphism := PreIsomorphism
  localic_description := LocalicDescription

/-- The specialization/order relation on the spectrum, represented by inclusion
of prime filters. -/
def SpecLE (A : DomainPrelocale.{u}) (F G : Spec A) : Prop :=
  F.1 ⊆ G.1

/-- The preorder on a prelocale spectrum, ordered by inclusion of prime filters. -/
@[reducible]
def spectrumPreorder (A : DomainPrelocale.{u}) : Preorder (Spec A) where
  le := SpecLE A
  le_refl := by
    intro F x hx
    exact hx
  le_trans := by
    intro F G H hFG hGH x hx
    exact hGH (hFG hx)

/-- The spectrum as an ordered domain for function-space statements. -/
def SpectrumOrderedDomain (A : DomainPrelocale.{u}) : Chapter4.OrderedDomain.{u} where
  carrier := Spec A
  preorder := spectrumPreorder A

/-- An isomorphism between the spectrum of a prelocale and a bifinite domain. -/
structure SpecDomainIso
    (A : DomainPrelocale.{u}) (D : Chapter4.BifiniteDomain.{u}) where
  toFun : Spec A → D.object.carrier
  invFun : D.object.carrier → Spec A
  left_inv : ∀ F : Spec A, invFun (toFun F) = F
  right_inv : ∀ x : D.object.carrier, toFun (invFun x) = x
  order_compatible :
    ∀ F G : Spec A, SpecLE A F G ↔ toFun F ≤ toFun G

/-- The principal filter `↑a` in a domain prelocale. -/
def PrincipalPrelocaleFilter (A : DomainPrelocale.{u}) (a : A.carrier) :
    Set A.carrier :=
  {b : A.carrier | A.le a b}

/-- Proof-shape data from the paragraph preceding Proposition 7.3.3: compact
principal spectrum points generated by `∨`-prime elements map to the least
compact element of the interpreted compact-open subset. -/
structure LocalicSpectrumCompactBehavior
    (A : DomainPrelocale.{u}) (D : Chapter4.BifiniteDomain.{u})
    (desc : LocalicDescription A D) (iso : SpecDomainIso A D) : Prop where
  compact_generator_maps_to_least :
    ∀ (a : A.carrier), A.C a → ∀ F : Spec A,
      F.1 = PrincipalPrelocaleFilter A a →
        @Chapter2.Compact D.object.carrier D.object.preorder (iso.toFun F) ∧
          iso.toFun F ∈ (desc.interpret a).carrier ∧
            ∀ x : D.object.carrier,
              x ∈ (desc.interpret a).carrier → iso.toFun F ≤ x

/-- Join-approximable relations between domain prelocales.  This is the
morphism class appearing in Theorem 7.3.4, stated with the explicit prelocale
operations rather than quotient lattices. -/
structure JoinApproximablePrelocaleRelation
    (A B : DomainPrelocale.{u}) : Type u where
  rel : A.carrier → B.carrier → Prop
  weakening :
    ∀ ⦃a a' : A.carrier⦄ ⦃b b' : B.carrier⦄,
      A.le a a' → B.le b' b → rel a b → rel a' b'
  finite_join_right :
    ∀ (a : A.carrier) (bs : List B.carrier),
      (∀ b : B.carrier, b ∈ bs → rel a b) →
        rel a (ListJoin B.sup B.zero bs)
  finite_meet_left :
    ∀ (as : List A.carrier) (b : B.carrier),
      (∀ a : A.carrier, a ∈ as → rel a b) →
        rel (ListMeet A.inf A.one as) b
  finite_join_cover :
    ∀ (as : List A.carrier) (b : B.carrier),
      rel (ListJoin A.sup A.zero as) b →
        ∃ bs : List B.carrier,
          RelEquiv B.le b (ListJoin B.sup B.zero bs) ∧
            ∀ y : B.carrier, y ∈ bs → ∃ x : A.carrier, x ∈ as ∧ rel x y

/-- Scott-continuous maps between bifinite domains, the morphism class on the
domain side of Theorem 7.3.4. -/
structure BifiniteScottContinuousMap
    (D E : Chapter4.BifiniteDomain.{u}) : Type u where
  toFun : D.object.carrier → E.object.carrier
  scott_continuous :
    @Chapter2.ScottContinuous
      D.object.carrier D.object.preorder
      E.object.carrier E.object.preorder toFun

/-- The Scott-continuous function space between two prelocale spectra. -/
abbrev SpectrumFunctionSpace (A B : DomainPrelocale.{u}) : Type u :=
  Chapter4.OrderedDomain.ContFunCarrier (SpectrumOrderedDomain A) (SpectrumOrderedDomain B)

/-- Isomorphism between the spectrum of a proposed function-space prelocale and
the function space between spectra. -/
structure FunctionSpaceSpectrumIso
    (A B F : DomainPrelocale.{u}) where
  toFun : Spec F → SpectrumFunctionSpace A B
  invFun : SpectrumFunctionSpace A B → Spec F
  left_inv : ∀ X : Spec F, invFun (toFun X) = X
  right_inv : ∀ f : SpectrumFunctionSpace A B, toFun (invFun f) = f
  order_compatible :
    ∀ X Y : Spec F, SpecLE F X Y ↔ toFun X ≤ toFun Y

/-- Definition 7.3.5: sub-prelocales. -/
structure SubPrelocale (A B : DomainPrelocale.{u}) where
  incl : A.carrier → B.carrier
  injective : Function.Injective incl
  preserves_order : ∀ ⦃a b : A.carrier⦄, A.le a b → B.le (incl a) (incl b)
  reflects_order : ∀ ⦃a b : A.carrier⦄, B.le (incl a) (incl b) → A.le a b
  preserves_sup : ∀ a b : A.carrier,
    RelEquiv B.le (incl (A.sup a b)) (B.sup (incl a) (incl b))
  preserves_inf : ∀ a b : A.carrier,
    RelEquiv B.le (incl (A.inf a b)) (B.inf (incl a) (incl b))
  preserves_bounds :
    RelEquiv B.le (incl A.zero) B.zero ∧ RelEquiv B.le (incl A.one) B.one
  preserves_primes : ∀ a : A.carrier, A.C a ↔ B.C (incl a)

/-- Definition 7.3.5, named book entry. -/
abbrev def_7_3_5_sub_prelocale (A B : DomainPrelocale.{u}) :=
  SubPrelocale A B

/-- The carrier formula `↑_B F` from Proposition 7.3.6. -/
def SubPrelocale.spectrumEmbeddingCarrier
    {A B : DomainPrelocale.{u}} (hAB : SubPrelocale A B) (F : Spec A) :
    Set B.carrier :=
  {b | ∃ a : A.carrier, a ∈ F.1 ∧ B.le (hAB.incl a) b}

/-- The carrier formula `G ∩ A` from Proposition 7.3.6. -/
def SubPrelocale.spectrumProjectionCarrier
    {A B : DomainPrelocale.{u}} (hAB : SubPrelocale A B) (G : Spec B) :
    Set A.carrier :=
  {a | hAB.incl a ∈ G.1}

/-- Embedding-projection pairs between spectra, with the concrete formulas
`e(F) = ↑_B F` and `p(G) = G ∩ A` from Proposition 7.3.6. -/
structure SpectrumEmbeddingProjection
    (A B : DomainPrelocale.{u}) (hAB : SubPrelocale A B) where
  embedding : Spec A → Spec B
  projection : Spec B → Spec A
  embedding_scott_continuous :
    @Chapter2.ScottContinuous
      (Spec A) (spectrumPreorder A) (Spec B) (spectrumPreorder B) embedding
  projection_scott_continuous :
    @Chapter2.ScottContinuous
      (Spec B) (spectrumPreorder B) (Spec A) (spectrumPreorder A) projection
  embedding_formula :
    ∀ F : Spec A, (embedding F).1 = hAB.spectrumEmbeddingCarrier F
  projection_formula :
    ∀ G : Spec B, (projection G).1 = hAB.spectrumProjectionCarrier G
  projection_embedding : ∀ F : Spec A, projection (embedding F) = F
  embedding_projection_below : ∀ G : Spec B, SpecLE B (embedding (projection G)) G

/-- Principal upper sets `↑c` in an ordered domain. -/
def PrincipalUpperSet (D : Chapter4.OrderedDomain.{u}) (c : D.carrier) :
    Set D.carrier :=
  {x | c ≤ x}

/-- Corollary 7.3.7 package: the domain embedding induced by localic
descriptions and a sub-prelocale inclusion, including the compact-generator
formula from the PDF. -/
structure SubPrelocaleDomainEmbedding
    (A B : DomainPrelocale.{u}) (D E : Chapter4.BifiniteDomain.{u})
    (descA : LocalicDescription A D) (descB : LocalicDescription B E)
    (hAB : SubPrelocale A B) where
  toFun : D.object.carrier → E.object.carrier
  scott_continuous :
    @Chapter3.ScottContinuous
      D.object.carrier E.object.carrier
      D.object.preorder E.object.preorder toFun
  injective : Function.Injective toFun
  order_embedding :
    ∀ x y : D.object.carrier, toFun x ≤ toFun y ↔ x ≤ y
  spectrum_embedding_projection :
    SpectrumEmbeddingProjection A B hAB
  source_spectrum_iso : SpecDomainIso A D
  target_spectrum_iso : SpecDomainIso B E
  factorizes_through_spectra :
    ∀ x : D.object.carrier,
      toFun x =
        target_spectrum_iso.toFun
          (spectrum_embedding_projection.embedding (source_spectrum_iso.invFun x))
  compact_generator_formula :
    ∀ (c : D.object.carrier) (d : E.object.carrier) (a : A.carrier),
      c ∈ Chapter4.CompactElements D.object →
        d ∈ Chapter4.CompactElements E.object →
          A.C a →
            (descA.interpret a).carrier = PrincipalUpperSet D.object c →
              (descB.interpret (hAB.incl a)).carrier =
                  PrincipalUpperSet E.object d →
                toFun c = d

/-- Function-space generators `(a -> b)`. -/
inductive FunctionSpaceGenerator (A B : DomainPrelocale.{u}) : Type u where
  | arrow : A.carrier → B.carrier → FunctionSpaceGenerator A B

/-- Naturality data for the function-space construction under sub-prelocale
inclusions.  The two concrete clauses match the PDF's final paragraph before
Theorem 7.3.10: arrow generators are sent to arrow generators, and the induced
spectrum map is the function-space embedding `f ↦ e' ∘ f ∘ e*`. -/
structure FunctionSpaceSubprelocaleNaturality
    (A A' B B' F F' : DomainPrelocale.{u})
    (hAA' : SubPrelocale A A') (hBB' : SubPrelocale B B')
    (hFF' : SubPrelocale F F')
    (sourceGenerator : FunctionSpaceGenerator A B → F.carrier)
    (targetGenerator : FunctionSpaceGenerator A' B' → F'.carrier) : Type u where
  source_spectrum_embedding : SpectrumEmbeddingProjection A A' hAA'
  target_spectrum_embedding : SpectrumEmbeddingProjection B B' hBB'
  function_spectrum_embedding : SpectrumEmbeddingProjection F F' hFF'
  source_spectrum_iso : FunctionSpaceSpectrumIso A B F
  target_spectrum_iso : FunctionSpaceSpectrumIso A' B' F'
  compact_generator_square :
    ∀ a : A.carrier, ∀ b : B.carrier,
      RelEquiv F'.le
        (hFF'.incl (sourceGenerator (FunctionSpaceGenerator.arrow a b)))
        (targetGenerator
          (FunctionSpaceGenerator.arrow (hAA'.incl a) (hBB'.incl b)))
  tau_square_commutes :
    ∀ X : Spec F, ∀ x : Spec A',
      target_spectrum_iso.toFun (function_spectrum_embedding.embedding X) x =
        target_spectrum_embedding.embedding
          (source_spectrum_iso.toFun X (source_spectrum_embedding.projection x))

/-- The finite joinability side-condition in the `(-> C)` rule of the function
space prelocale.  The list-based statement mirrors the PDF's finite-index
condition: every finite subfamily has a covering subfamily whose domain meet is
equivalent to a domain join and whose codomain components are pointwise above
the selected codomain components. -/
def FunctionSpaceJoinableFamily
    (A B : DomainPrelocale.{u}) (pairs : List (A.carrier × B.carrier)) : Prop :=
  ∀ K : List (A.carrier × B.carrier),
    (∀ p : A.carrier × B.carrier, p ∈ K → p ∈ pairs) →
      ∃ L : List (A.carrier × B.carrier),
        (∀ p : A.carrier × B.carrier, p ∈ L → p ∈ pairs) ∧
          RelEquiv A.le
            (ListMeet A.inf A.one (K.map Prod.fst))
            (ListJoin A.sup A.zero (L.map Prod.fst)) ∧
            ∀ k : A.carrier × B.carrier, k ∈ K →
              ∀ l : A.carrier × B.carrier, l ∈ L → B.le k.2 l.2

/-- A localic package for the function-space construction. -/
structure FunctionSpacePrelocaleDescription (A B : DomainPrelocale.{u}) where
  prelocale : DomainPrelocale.{u}
  generator : FunctionSpaceGenerator A B → prelocale.carrier
  arrow_meet_codomain :
    ∀ (a : A.carrier) (bs : List B.carrier),
      RelEquiv prelocale.le
        (generator (FunctionSpaceGenerator.arrow a (ListMeet B.inf B.one bs)))
        (ListMeet prelocale.inf prelocale.one
          (bs.map fun b => generator (FunctionSpaceGenerator.arrow a b)))
  arrow_join_domain :
    ∀ (as : List A.carrier) (b : B.carrier),
      RelEquiv prelocale.le
        (generator (FunctionSpaceGenerator.arrow (ListJoin A.sup A.zero as) b))
        (ListMeet prelocale.inf prelocale.one
          (as.map fun a => generator (FunctionSpaceGenerator.arrow a b)))
  distributive :
    ∀ x y z : prelocale.carrier,
      RelEquiv prelocale.le
        (prelocale.inf x (prelocale.sup y z))
        (prelocale.sup (prelocale.inf x y) (prelocale.inf x z))
  arrow_join_codomain_of_prime :
    ∀ (a : A.carrier), A.C a → ∀ bs : List B.carrier,
      RelEquiv prelocale.le
        (generator (FunctionSpaceGenerator.arrow a (ListJoin B.sup B.zero bs)))
        (ListJoin prelocale.sup prelocale.zero
          (bs.map fun b => generator (FunctionSpaceGenerator.arrow a b)))
  arrow_order_rule :
    ∀ ⦃a b : A.carrier⦄ ⦃a' b' : B.carrier⦄,
      A.le b a → B.le a' b' →
        prelocale.le
          (generator (FunctionSpaceGenerator.arrow a a'))
          (generator (FunctionSpaceGenerator.arrow b b'))
  arrow_prime_rule :
    ∀ pairs : List (A.carrier × B.carrier),
      (∀ p : A.carrier × B.carrier, p ∈ pairs → A.C p.1 ∧ B.C p.2) →
        FunctionSpaceJoinableFamily A B pairs →
          prelocale.C
            (ListMeet prelocale.inf prelocale.one
              (pairs.map fun p => generator (FunctionSpaceGenerator.arrow p.1 p.2)))
  spectrum_iso : FunctionSpaceSpectrumIso A B prelocale
  generator_interpretation :
    ∀ a : A.carrier, ∀ b : B.carrier, ∀ F : Spec prelocale,
      generator (FunctionSpaceGenerator.arrow a b) ∈ F.1 ↔
        ∀ x : Spec A, a ∈ x.1 → b ∈ (spectrum_iso.toFun F x).1
  prime_generation :
    ∀ p : prelocale.carrier, prelocale.C p →
      ∃ gens : List (FunctionSpaceGenerator A B),
        RelEquiv prelocale.le
          (ListMeet prelocale.inf prelocale.one (gens.map generator)) p
  prime_completeness :
    ∀ p q : prelocale.carrier, prelocale.C p → prelocale.C q →
      (∀ F : Spec prelocale, p ∈ F.1 → q ∈ F.1) → prelocale.le p q
  prime_definability :
    ∀ f : SpectrumFunctionSpace A B, ∃ F : Spec prelocale, spectrum_iso.toFun F = f
  least_prelocale :
    ∃ I : DomainPrelocale.{u}, Nonempty (SubPrelocale I prelocale)
  naturality_under_subprelocales :
    ∀ {A' B' : DomainPrelocale.{u}},
      (hAA' : SubPrelocale A A') → (hBB' : SubPrelocale B B') →
        ∃ F' : DomainPrelocale.{u}, ∃ hFF' : SubPrelocale prelocale F',
          ∃ targetGenerator : FunctionSpaceGenerator A' B' → F'.carrier,
            Nonempty
              (FunctionSpaceSubprelocaleNaturality
                A A' B B' prelocale F' hAA' hBB' hFF' generator
                targetGenerator)

/-- The compact-open subbasis `(A => O)` for the function space. -/
def FunctionSpacePredicate
    (D E : Chapter4.OrderedDomain.{u})
    (A : Set D.carrier) (O : Set E.carrier) :
    Set (Chapter4.OrderedDomain.ContFunCarrier D E) :=
  {f | ∀ x : D.carrier, x ∈ A → f.toFun x ∈ O}

/-- Compact subsets used in the compact-open subbasis for function spaces. -/
structure CompactSubset (D : Chapter4.OrderedDomain.{u}) where
  carrier : Set D.carrier
  compact : ScottCompactSet D carrier

/-- Scott-open subsets used in the compact-open subbasis for function spaces. -/
structure ScottOpenSubset (D : Chapter4.OrderedDomain.{u}) where
  carrier : Set D.carrier
  scott_open : @Chapter2.ScottOpen D.carrier D.preorder carrier

/-- The compact-open topology on a function-space object, generated by the
subbasic predicates `(K => O)` with `K` compact and `O` Scott-open. -/
inductive CompactOpenFunctionSpaceOpen
    (D E : Chapter4.OrderedDomain.{u})
    : Set (Chapter4.OrderedDomain.ContFunCarrier D E) → Prop
  | univ : CompactOpenFunctionSpaceOpen D E Set.univ
  | subbasic (K : CompactSubset D) (O : ScottOpenSubset E) :
      CompactOpenFunctionSpaceOpen D E
        (FunctionSpacePredicate D E K.carrier O.carrier)
  | inter {U V : Set (Chapter4.OrderedDomain.ContFunCarrier D E)} :
      CompactOpenFunctionSpaceOpen D E U →
        CompactOpenFunctionSpaceOpen D E V →
          CompactOpenFunctionSpaceOpen D E (U ∩ V)
  | sUnion {S : Set (Set (Chapter4.OrderedDomain.ContFunCarrier D E))} :
      (∀ U ∈ S, CompactOpenFunctionSpaceOpen D E U) →
        CompactOpenFunctionSpaceOpen D E (⋃₀ S)

/-- Lemma 7.3.9 conclusion package: the predicate `(A => A')` is a compact-open
subset of the bifinite function space. -/
structure FunctionSpacePredicateCompactOpen
    (D E : Chapter4.BifiniteDomain.{u})
    (A : CompactOpenSet D.object) (A' : CompactOpenSet E.object) : Prop where
  scott_open :
    @Chapter2.ScottOpen
      (Chapter4.OrderedDomain.ContFunCarrier D.object E.object)
      (Chapter4.OrderedDomain.contFunPreorder D.object E.object)
      (FunctionSpacePredicate D.object E.object A.carrier A'.carrier)
  compact :
    ScottCompactSet
      (Chapter4.OrderedDomain.functionSpace D.object E.object)
      (FunctionSpacePredicate D.object E.object A.carrier A'.carrier)
  compact_open_topology :
    CompactOpenFunctionSpaceOpen D.object E.object
      (FunctionSpacePredicate D.object E.object A.carrier A'.carrier)

/-- The predicate `(A => A')` is one of the subbasic compact-open predicates
by definition of the compact-open topology on the function space. -/
theorem functionSpacePredicate_compactOpenTopology
    (D E : Chapter4.BifiniteDomain.{u})
    (A : CompactOpenSet D.object) (A' : CompactOpenSet E.object) :
    CompactOpenFunctionSpaceOpen D.object E.object
      (FunctionSpacePredicate D.object E.object A.carrier A'.carrier) := by
  exact CompactOpenFunctionSpaceOpen.subbasic
    ⟨A.carrier, A.compact⟩ ⟨A'.carrier, A'.scott_open⟩

/-- A family of opens is a base for the Scott topology of an ordered domain. -/
def ScottTopologyBase (D : Chapter4.OrderedDomain.{u})
    (B : Set (Set D.carrier)) : Prop :=
  ∀ U : Set D.carrier, @Chapter2.ScottOpen D.carrier D.preorder U →
    ∀ x : D.carrier, x ∈ U → ∃ V ∈ B, x ∈ V ∧ V ⊆ U

/-- The compact-open observation represented by a prelocale element on the
spectrum of that prelocale. -/
def PrelocaleObservation (A : DomainPrelocale.{u}) (a : A.carrier) :
    Set (Spec A) :=
  {F | a ∈ F.1}

/-- Plotkin universal modality `A(O)`: every run lies in `O`. -/
def PlotkinAllRuns (D : Chapter4.OrderedDomain.{u}) (O : Set D.carrier) :
    Set (Chapter6.Lens D) :=
  {L | L.carrier ⊆ O}

/-- Plotkin existential modality `E(O)`: some run lies in `O`. -/
def PlotkinSomeRun (D : Chapter4.OrderedDomain.{u}) (O : Set D.carrier) :
    Set (Chapter6.Lens D) :=
  {L | ∃ x : D.carrier, x ∈ L.carrier ∧ x ∈ O}

/-- The lens representation of the Plotkin powerdomain used in the localic
Plotkin powerlocale statements. -/
abbrev PlotkinLensRepresentation (D : Chapter4.OrderedDomain.{u}) : Type (u + 1) :=
  Chapter6.LensPowerdomainRepresentation D Chapter6.PowerdomainKind.plotkin
    (@Chapter6.LensEgliMilner D) (Chapter6.PlainConvexClosure D)

/-- Pull a lens predicate back along a chosen representation of the Plotkin
powerdomain. -/
def LensPredicateCarrier {D : Chapter4.OrderedDomain.{u}}
    (rep : PlotkinLensRepresentation D) (S : Set (Chapter6.Lens D)) :
    Set rep.powerdomain.carrier.carrier :=
  {p | rep.equiv p ∈ S}

/-- The upper set of a lens inside a Plotkin powerdomain representation, using
the ordinary Egli-Milner order on lenses. -/
def LensUpperSetInPlotkinPowerdomain {D : Chapter4.OrderedDomain.{u}}
    (rep : PlotkinLensRepresentation D) (K : Chapter6.Lens D) :
    Set rep.powerdomain.carrier.carrier :=
  {p | Chapter6.LensEgliMilner K (rep.equiv p)}

/-- The compact-open `↑u` generated by a finite list of compact elements. -/
def FiniteCompactUpperClosure
    (D : Chapter4.OrderedDomain.{u}) (xs : List D.carrier) : Set D.carrier :=
  {x | ∃ c : D.carrier, c ∈ xs ∧ c ≤ x}

/-- The concrete formula from Lemma 7.3.11:
`↑Cx(u) = A(↑u) ∩ ⋂_{c∈u} E(↑c)`, pulled back along the chosen lens
representation of the Plotkin powerdomain. -/
def PlotkinCompactLensUpperDecomposition
    {D : Chapter4.OrderedDomain.{u}} (rep : PlotkinLensRepresentation D)
    (K : Chapter6.Lens D) (xs : List D.carrier) : Prop :=
  LensUpperSetInPlotkinPowerdomain rep K =
    LensPredicateCarrier rep (PlotkinAllRuns D (FiniteCompactUpperClosure D xs)) ∩
      ⋂₀ {U : Set rep.powerdomain.carrier.carrier |
        ∃ c : D.carrier, c ∈ xs ∧
          U = LensPredicateCarrier rep (PlotkinSomeRun D (PrincipalUpperSet D c))}

/-- The modal opens generated by `A(O)` and `E(O)` for compact-open
observations `O`. -/
def PlotkinModalOpenFamily {D : Chapter4.OrderedDomain.{u}}
    (rep : PlotkinLensRepresentation D) :
    Set (Set rep.powerdomain.carrier.carrier) :=
  {U | ∃ O : CompactOpenSet D,
    U = LensPredicateCarrier rep (PlotkinAllRuns D O.carrier) ∨
      U = LensPredicateCarrier rep (PlotkinSomeRun D O.carrier)}

/-- Lemma 7.3.11 package: for each compact-open observation `O`, the Plotkin
modalities `A(O)` and `E(O)` are compact-open in the Plotkin powerdomain, and
the modalities generated by compact-open observations form a Scott base. -/
structure PlotkinModalCompactOpenPackage
    (D : Chapter4.BifiniteDomain.{u}) (O : CompactOpenSet D.object) where
  representation : PlotkinLensRepresentation D.object
  allRuns : Set representation.powerdomain.carrier.carrier
  someRun : Set representation.powerdomain.carrier.carrier
  allRuns_def :
    allRuns =
      LensPredicateCarrier representation (PlotkinAllRuns D.object O.carrier)
  someRun_def :
    someRun =
      LensPredicateCarrier representation (PlotkinSomeRun D.object O.carrier)
  allRuns_scott_open :
    @Chapter2.ScottOpen representation.powerdomain.carrier.carrier
      representation.powerdomain.carrier.preorder allRuns
  someRun_scott_open :
    @Chapter2.ScottOpen representation.powerdomain.carrier.carrier
      representation.powerdomain.carrier.preorder someRun
  allRuns_compact :
    ScottCompactSet representation.powerdomain.carrier allRuns
  someRun_compact :
    ScottCompactSet representation.powerdomain.carrier someRun
  modalities_form_base :
    ScottTopologyBase representation.powerdomain.carrier
      (PlotkinModalOpenFamily representation)
  compact_lens_upper_decomposition :
    ∀ (K : Chapter6.Lens D.object) (xs : List D.object.carrier),
      xs ≠ [] →
        (∀ c : D.object.carrier, c ∈ xs → c ∈ Chapter4.CompactElements D.object) →
          K.carrier = Chapter6.PlainConvexClosure D.object
            ({x : D.object.carrier | x ∈ xs}) →
            PlotkinCompactLensUpperDecomposition representation K xs

/-- Plotkin powerlocale generators `box a` and `diamond a`. -/
inductive PowerlocaleGenerator (A : DomainPrelocale.{u}) : Type u where
  | box : A.carrier → PowerlocaleGenerator A
  | diamond : A.carrier → PowerlocaleGenerator A

/-- A spectrum/powerdomain isomorphism for the Plotkin powerlocale theorem. -/
structure PlotkinPowerlocaleSpectrumIso
    (A P : DomainPrelocale.{u}) where
  representation : PlotkinLensRepresentation (SpectrumOrderedDomain A)
  toFun : Spec P → representation.powerdomain.carrier.carrier
  invFun : representation.powerdomain.carrier.carrier → Spec P
  left_inv : ∀ F : Spec P, invFun (toFun F) = F
  right_inv : ∀ L : representation.powerdomain.carrier.carrier, toFun (invFun L) = L
  order_compatible :
    ∀ F G : Spec P, SpecLE P F G ↔ toFun F ≤ toFun G

/-- The `∨`-prime Plotkin generator term
`box (∨ xs) ∧ ⋀_{x∈xs} diamond x` used in the generation rule. -/
def PlotkinPrimeTerm (A P : DomainPrelocale.{u})
    (generator : PowerlocaleGenerator A → P.carrier)
    (xs : List A.carrier) : P.carrier :=
  P.inf
    (generator (PowerlocaleGenerator.box (ListJoin A.sup A.zero xs)))
    (ListMeet P.inf P.one
      (xs.map (fun a => generator (PowerlocaleGenerator.diamond a))))

/-- Definition 7.3.12: Plotkin powerlocales. -/
structure PlotkinPowerlocaleDescription (A : DomainPrelocale.{u}) where
  prelocale : DomainPrelocale.{u}
  generator : PowerlocaleGenerator A → prelocale.carrier
  spectrum_iso : PlotkinPowerlocaleSpectrumIso A prelocale
  box_interpretation :
    ∀ a : A.carrier, ∀ F : Spec prelocale,
      generator (PowerlocaleGenerator.box a) ∈ F.1 ↔
        (spectrum_iso.representation.equiv (spectrum_iso.toFun F)).carrier ⊆
          PrelocaleObservation A a
  diamond_interpretation :
    ∀ a : A.carrier, ∀ F : Spec prelocale,
      generator (PowerlocaleGenerator.diamond a) ∈ F.1 ↔
        ∃ x : Spec A,
          (x : (SpectrumOrderedDomain A).carrier) ∈
              (spectrum_iso.representation.equiv (spectrum_iso.toFun F)).carrier ∧
            x ∈ PrelocaleObservation A a
  box_meet_axiom :
    ∀ xs : List A.carrier,
      RelEquiv prelocale.le
        (generator (PowerlocaleGenerator.box (ListMeet A.inf A.one xs)))
        (ListMeet prelocale.inf prelocale.one
          (xs.map (fun a => generator (PowerlocaleGenerator.box a))))
  box_zero_axiom :
    RelEquiv prelocale.le
      (generator (PowerlocaleGenerator.box A.zero)) prelocale.zero
  diamond_join_axiom :
    ∀ xs : List A.carrier,
      RelEquiv prelocale.le
        (generator (PowerlocaleGenerator.diamond (ListJoin A.sup A.zero xs)))
        (ListJoin prelocale.sup prelocale.zero
          (xs.map (fun a => generator (PowerlocaleGenerator.diamond a))))
  diamond_one_axiom :
    RelEquiv prelocale.le
      (generator (PowerlocaleGenerator.diamond A.one)) prelocale.one
  box_join_axiom :
    ∀ a b : A.carrier,
      prelocale.le
        (generator (PowerlocaleGenerator.box (A.sup a b)))
        (prelocale.sup
          (generator (PowerlocaleGenerator.box a))
          (generator (PowerlocaleGenerator.diamond b)))
  diamond_meet_axiom :
    ∀ a b : A.carrier,
      prelocale.le
        (prelocale.inf
          (generator (PowerlocaleGenerator.box a))
          (generator (PowerlocaleGenerator.diamond b)))
        (generator (PowerlocaleGenerator.diamond (A.inf a b)))
  derived_box_join_axiom :
    ∀ a b : A.carrier,
      RelEquiv prelocale.le
        (generator (PowerlocaleGenerator.box (A.sup a b)))
        (prelocale.sup
          (generator (PowerlocaleGenerator.box a))
          (prelocale.inf
            (generator (PowerlocaleGenerator.box (A.sup a b)))
            (generator (PowerlocaleGenerator.diamond b))))
  derived_diamond_meet_axiom :
    ∀ a b : A.carrier,
      RelEquiv prelocale.le
        (prelocale.inf
          (generator (PowerlocaleGenerator.box a))
          (generator (PowerlocaleGenerator.diamond b)))
        (prelocale.inf
          (generator (PowerlocaleGenerator.box a))
          (generator (PowerlocaleGenerator.diamond (A.inf a b))))
  distributivity_axiom :
    ∀ x y z : prelocale.carrier,
      RelEquiv prelocale.le
        (prelocale.inf x (prelocale.sup y z))
        (prelocale.sup (prelocale.inf x y) (prelocale.inf x z))
  monotonicity_rule :
    ∀ a b : A.carrier, A.le a b →
      prelocale.le (generator (PowerlocaleGenerator.box a))
        (generator (PowerlocaleGenerator.box b)) ∧
      prelocale.le (generator (PowerlocaleGenerator.diamond a))
        (generator (PowerlocaleGenerator.diamond b))
  prime_rule :
    ∀ xs : List A.carrier, xs ≠ [] → (∀ a : A.carrier, a ∈ xs → A.C a) →
      prelocale.C (PlotkinPrimeTerm A prelocale generator xs)
  prime_generation :
    ∀ p : prelocale.carrier, prelocale.C p →
      ∃ xs : List A.carrier,
        xs ≠ [] ∧ (∀ a : A.carrier, a ∈ xs → A.C a) ∧
          RelEquiv prelocale.le (PlotkinPrimeTerm A prelocale generator xs) p
  prime_order_reflecting :
    ∀ p q : prelocale.carrier, prelocale.C p → prelocale.C q →
      (∀ F : Spec prelocale, p ∈ F.1 → q ∈ F.1) → prelocale.le p q
  prime_term_interpretation :
    ∀ xs : List A.carrier, ∀ F : Spec prelocale,
      PlotkinPrimeTerm A prelocale generator xs ∈ F.1 ↔
        (spectrum_iso.representation.equiv (spectrum_iso.toFun F)).carrier ⊆
          PrelocaleObservation A (ListJoin A.sup A.zero xs) ∧
        ∀ a : A.carrier, a ∈ xs →
          ∃ x : Spec A,
            (x : (SpectrumOrderedDomain A).carrier) ∈
                (spectrum_iso.representation.equiv (spectrum_iso.toFun F)).carrier ∧
              x ∈ PrelocaleObservation A a
  naturality_under_subprelocales :
    ∀ {B : DomainPrelocale.{u}}, SubPrelocale A B →
      ∃ Q : DomainPrelocale.{u}, Nonempty (SubPrelocale prelocale Q)

/-- Definition 7.3.12, named book entry. -/
abbrev def_7_3_12_plotkin_powerlocale :=
  PlotkinPowerlocaleDescription

/-- Naturality data for Theorem 7.3.13.  It records that a sub-prelocale
`A P B` induces a compatible sub-prelocale between the corresponding Plotkin
powerlocales, that `box`/`diamond` generators are preserved, and that the
spectrum isomorphisms commute with the induced powerdomain map. -/
structure PlotkinPowerlocaleNaturality
    {A B : DomainPrelocale.{u}} (hAB : SubPrelocale A B)
    (PA : PlotkinPowerlocaleDescription A)
    (PB : PlotkinPowerlocaleDescription B) where
  prelocale_inclusion : SubPrelocale PA.prelocale PB.prelocale
  generator_box_compatible :
    ∀ a : A.carrier,
      RelEquiv PB.prelocale.le
        (prelocale_inclusion.incl (PA.generator (PowerlocaleGenerator.box a)))
        (PB.generator (PowerlocaleGenerator.box (hAB.incl a)))
  generator_diamond_compatible :
    ∀ a : A.carrier,
      RelEquiv PB.prelocale.le
        (prelocale_inclusion.incl (PA.generator (PowerlocaleGenerator.diamond a)))
        (PB.generator (PowerlocaleGenerator.diamond (hAB.incl a)))
  spectrum_embedding :
    SpectrumEmbeddingProjection PA.prelocale PB.prelocale prelocale_inclusion
  powerdomain_embedding :
    PA.spectrum_iso.representation.powerdomain.carrier.carrier →
      PB.spectrum_iso.representation.powerdomain.carrier.carrier
  spectrum_iso_naturality :
    ∀ F : Spec PA.prelocale,
      powerdomain_embedding (PA.spectrum_iso.toFun F) =
        PB.spectrum_iso.toFun (spectrum_embedding.embedding F)

/-- Theorem 7.3.13 data package: a Plotkin powerlocale for every domain
prelocale, together with naturality for sub-prelocale inclusions. -/
structure PlotkinPowerlocaleRepresentationData : Type (u + 2) where
  description : ∀ A : DomainPrelocale.{u}, PlotkinPowerlocaleDescription A
  naturality :
    ∀ {A B : DomainPrelocale.{u}} (hAB : SubPrelocale A B),
      Nonempty (PlotkinPowerlocaleNaturality hAB (description A) (description B))

/-- Chains of domain prelocales under the sub-prelocale relation. -/
structure PrelocaleChain where
  obj : Nat → DomainPrelocale.{u}
  step : ∀ n : Nat, SubPrelocale (obj n) (obj (n + 1))

/-- Spectrum-level bilimit data for a chain of prelocales.  The compatible
sequences model the bilimit of the spectra of the stages. -/
structure PrelocaleChainSpectrumBilimit
    (C : PrelocaleChain.{u}) (U : DomainPrelocale.{u}) where
  stageProjection :
    ∀ n m : Nat, n ≤ m → Spec (C.obj m) → Spec (C.obj n)
  compatible_sequences : Set (∀ n : Nat, Spec (C.obj n))
  compatible_iff :
    ∀ s : ∀ n : Nat, Spec (C.obj n),
      s ∈ compatible_sequences ↔
        ∀ n m : Nat, ∀ hnm : n ≤ m, stageProjection n m hnm (s m) = s n
  toSequence : Spec U → ∀ n : Nat, Spec (C.obj n)
  fromCompatibleSequence :
    {s : ∀ n : Nat, Spec (C.obj n) // s ∈ compatible_sequences} → Spec U
  to_compatible : ∀ F : Spec U, toSequence F ∈ compatible_sequences
  left_inv :
    ∀ F : Spec U, fromCompatibleSequence ⟨toSequence F, to_compatible F⟩ = F
  right_inv :
    ∀ s : {s : ∀ n : Nat, Spec (C.obj n) // s ∈ compatible_sequences},
      toSequence (fromCompatibleSequence s) = s.1
  order_compatible :
    ∀ F G : Spec U,
      SpecLE U F G ↔
        ∀ n : Nat, SpecLE (C.obj n) (toSequence F n) (toSequence G n)

/-- A localic bilimit/union description for a prelocale chain. -/
structure PrelocaleChainBilimitDescription (C : PrelocaleChain.{u}) where
  union : DomainPrelocale.{u}
  includes : ∀ n : Nat, SubPrelocale (C.obj n) union
  stage_inclusion : ∀ n m : Nat, n ≤ m → SubPrelocale (C.obj n) (C.obj m)
  stage_inclusion_refl :
    ∀ n : Nat, ∀ a : (C.obj n).carrier,
      (stage_inclusion n n (le_rfl : n ≤ n)).incl a = a
  stage_inclusion_step :
    ∀ n : Nat, ∀ a : (C.obj n).carrier,
      (stage_inclusion n (n + 1) (Nat.le_succ n)).incl a = (C.step n).incl a
  stage_inclusion_comp :
    ∀ n m k : Nat, ∀ hnm : n ≤ m, ∀ hmk : m ≤ k,
      ∀ a : (C.obj n).carrier,
        (stage_inclusion m k hmk).incl ((stage_inclusion n m hnm).incl a) =
          (stage_inclusion n k (Nat.le_trans hnm hmk)).incl a
  stage_spectrum_embedding :
    ∀ n m : Nat, ∀ hnm : n ≤ m,
      SpectrumEmbeddingProjection (C.obj n) (C.obj m) (stage_inclusion n m hnm)
  includes_compatible :
    ∀ n m : Nat, ∀ hnm : n ≤ m, ∀ a : (C.obj n).carrier,
      (includes m).incl ((stage_inclusion n m hnm).incl a) = (includes n).incl a
  union_spectrum_embedding :
    ∀ n : Nat, SpectrumEmbeddingProjection (C.obj n) union (includes n)
  union_generated :
    ∀ u : union.carrier,
      ∃ n : Nat, ∃ a : (C.obj n).carrier,
        RelEquiv union.le ((includes n).incl a) u
  finite_subsets_enter_stage :
    ∀ S : Set union.carrier, S.Finite →
      ∃ n : Nat,
        ∀ s : union.carrier, s ∈ S →
          ∃ a : (C.obj n).carrier, RelEquiv union.le ((includes n).incl a) s
  spectrum_bilimit : PrelocaleChainSpectrumBilimit C union
  stage_projection_formula :
    ∀ n m : Nat, ∀ hnm : n ≤ m,
      spectrum_bilimit.stageProjection n m hnm =
        (stage_spectrum_embedding n m hnm).projection
  to_sequence_formula :
    ∀ F : Spec union, ∀ n : Nat,
      spectrum_bilimit.toSequence F n =
        (union_spectrum_embedding n).projection F
  stage_domain : Nat → Chapter4.BifiniteDomain.{u}
  stage_description :
    ∀ n : Nat, LocalicDescription (C.obj n) (stage_domain n)
  bilimit_domain : Chapter4.BifiniteDomain.{u}
  union_description : LocalicDescription union bilimit_domain
  stage_domain_embedding :
    ∀ n m : Nat, ∀ hnm : n ≤ m,
      SubPrelocaleDomainEmbedding
        (C.obj n) (C.obj m) (stage_domain n) (stage_domain m)
        (stage_description n) (stage_description m) (stage_inclusion n m hnm)
  stage_domain_embedding_comp :
    ∀ n m k : Nat, ∀ hnm : n ≤ m, ∀ hmk : m ≤ k,
      ∀ x : (stage_domain n).object.carrier,
        (stage_domain_embedding n k (Nat.le_trans hnm hmk)).toFun x =
          (stage_domain_embedding m k hmk).toFun
            ((stage_domain_embedding n m hnm).toFun x)
  union_stage_embedding :
    ∀ n : Nat,
      SubPrelocaleDomainEmbedding
        (C.obj n) union (stage_domain n) bilimit_domain
        (stage_description n) union_description (includes n)
  union_stage_embedding_factorizes :
    ∀ n m : Nat, ∀ hnm : n ≤ m,
      ∀ x : (stage_domain n).object.carrier,
        (union_stage_embedding n).toFun x =
          (union_stage_embedding m).toFun
            ((stage_domain_embedding n m hnm).toFun x)
  bilimit_compact_from_stage :
    ∀ c : bilimit_domain.object.carrier,
      c ∈ Chapter4.CompactElements bilimit_domain.object →
        ∃ n : Nat, ∃ cn : (stage_domain n).object.carrier,
          cn ∈ Chapter4.CompactElements (stage_domain n).object ∧
            (union_stage_embedding n).toFun cn = c

end Chapter7
end AbramskyJung

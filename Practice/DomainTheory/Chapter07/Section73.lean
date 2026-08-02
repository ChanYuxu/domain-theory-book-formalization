import Practice.DomainTheory.Chapter06.Section62
import Practice.DomainTheory.Chapter07.Section72

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 7.3

The localic/logical viewpoint: domain prelocales, constructions on compact-open
lattices, and the syntax of types, properties, and terms.

Semantic audit note: the PDF-facing localic spectrum, sub-prelocale,
function-space, bilimit, type interpretation, property-language, and domain
logic results are visible proof-debt declarations where the PDF proof has not
yet been translated.  Auxiliary packages record the intended data.  Known
modeling gaps, such as the weak Plotkin sub-prelocale naturality witness and the
variable-free closed-type fragment, are recorded in `formalization_status.md`.
-/

universe u v

namespace AbramskyJung
namespace Chapter7

/-- Equivalence induced by a preorder relation. -/
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

/-- Type expressions for the domain-logic language. -/
inductive TypeExpr (Var : Type u) : Type u where
  | one : TypeExpr Var
  | var : Var → TypeExpr Var
  | arr : TypeExpr Var → TypeExpr Var → TypeExpr Var
  | prod : TypeExpr Var → TypeExpr Var → TypeExpr Var
  | sum : TypeExpr Var → TypeExpr Var → TypeExpr Var
  | lift : TypeExpr Var → TypeExpr Var
  | plotkin : TypeExpr Var → TypeExpr Var
  | recTy : Var → TypeExpr Var → TypeExpr Var

/-- Current variable-free closed-fragment representation, using `Empty` as the
variable type.  Recursive binders are still represented in the general
`TypeExpr` interface and tracked by `TypeExpr.RecUnfolding`. -/
abbrev ClosedTypeExpr : Type :=
  TypeExpr Empty

/-- Free variables of type expressions; `recTy` binds its variable. -/
inductive TypeExpr.FreeVar {Var : Type u} (X : Var) :
    TypeExpr Var → Prop where
  | var : TypeExpr.FreeVar X (.var X)
  | arr_left {σ τ : TypeExpr Var} :
      TypeExpr.FreeVar X σ → TypeExpr.FreeVar X (.arr σ τ)
  | arr_right {σ τ : TypeExpr Var} :
      TypeExpr.FreeVar X τ → TypeExpr.FreeVar X (.arr σ τ)
  | prod_left {σ τ : TypeExpr Var} :
      TypeExpr.FreeVar X σ → TypeExpr.FreeVar X (.prod σ τ)
  | prod_right {σ τ : TypeExpr Var} :
      TypeExpr.FreeVar X τ → TypeExpr.FreeVar X (.prod σ τ)
  | sum_left {σ τ : TypeExpr Var} :
      TypeExpr.FreeVar X σ → TypeExpr.FreeVar X (.sum σ τ)
  | sum_right {σ τ : TypeExpr Var} :
      TypeExpr.FreeVar X τ → TypeExpr.FreeVar X (.sum σ τ)
  | lift {σ : TypeExpr Var} :
      TypeExpr.FreeVar X σ → TypeExpr.FreeVar X (.lift σ)
  | plotkin {σ : TypeExpr Var} :
      TypeExpr.FreeVar X σ → TypeExpr.FreeVar X (.plotkin σ)
  | rec_body {Y : Var} {body : TypeExpr Var} :
      Y ≠ X → TypeExpr.FreeVar X body → TypeExpr.FreeVar X (.recTy Y body)

/-- Capture-aware substitution relation for type expressions.  The constructor
`rec_same` stops below a binder for the substituted variable, while `rec_other`
continues below distinct binders only when the binder is fresh for the
replacement expression. -/
inductive TypeExpr.Subst {Var : Type u} (X : Var) (replacement : TypeExpr Var) :
    TypeExpr Var → TypeExpr Var → Prop where
  | one : TypeExpr.Subst X replacement .one .one
  | var_same : TypeExpr.Subst X replacement (.var X) replacement
  | var_other {Y : Var} : Y ≠ X →
      TypeExpr.Subst X replacement (.var Y) (.var Y)
  | arr {σ τ σ' τ' : TypeExpr Var} :
      TypeExpr.Subst X replacement σ σ' →
        TypeExpr.Subst X replacement τ τ' →
          TypeExpr.Subst X replacement (.arr σ τ) (.arr σ' τ')
  | prod {σ τ σ' τ' : TypeExpr Var} :
      TypeExpr.Subst X replacement σ σ' →
        TypeExpr.Subst X replacement τ τ' →
          TypeExpr.Subst X replacement (.prod σ τ) (.prod σ' τ')
  | sum {σ τ σ' τ' : TypeExpr Var} :
      TypeExpr.Subst X replacement σ σ' →
        TypeExpr.Subst X replacement τ τ' →
          TypeExpr.Subst X replacement (.sum σ τ) (.sum σ' τ')
  | lift {σ σ' : TypeExpr Var} :
      TypeExpr.Subst X replacement σ σ' →
        TypeExpr.Subst X replacement (.lift σ) (.lift σ')
  | plotkin {σ σ' : TypeExpr Var} :
      TypeExpr.Subst X replacement σ σ' →
        TypeExpr.Subst X replacement (.plotkin σ) (.plotkin σ')
  | rec_same (body : TypeExpr Var) :
      TypeExpr.Subst X replacement (.recTy X body) (.recTy X body)
  | rec_other {Y : Var} {body body' : TypeExpr Var} :
      Y ≠ X →
        ¬ TypeExpr.FreeVar Y replacement →
        TypeExpr.Subst X replacement body body' →
          TypeExpr.Subst X replacement (.recTy Y body) (.recTy Y body')

/-- The body type of `rec X. σ`, after substituting the recursive type for `X`. -/
def TypeExpr.RecUnfolding {Var : Type u} (X : Var) (σ τ : TypeExpr Var) : Prop :=
  TypeExpr.Subst X (.recTy X σ) σ τ

/-- Properties associated with type expressions. -/
inductive PropertyExpr (Var : Type u) : TypeExpr Var → Type u where
  | truth {σ : TypeExpr Var} : PropertyExpr Var σ
  | falsity {σ : TypeExpr Var} : PropertyExpr Var σ
  | conj {σ : TypeExpr Var} :
      PropertyExpr Var σ → PropertyExpr Var σ → PropertyExpr Var σ
  | disj {σ : TypeExpr Var} :
      PropertyExpr Var σ → PropertyExpr Var σ → PropertyExpr Var σ
  | arrow {σ τ : TypeExpr Var} :
      PropertyExpr Var σ → PropertyExpr Var τ → PropertyExpr Var (.arr σ τ)
  | product {σ τ : TypeExpr Var} :
      PropertyExpr Var σ → PropertyExpr Var τ → PropertyExpr Var (.prod σ τ)
  | sumLeft {σ τ : TypeExpr Var} :
      PropertyExpr Var σ → PropertyExpr Var (.sum σ τ)
  | sumRight {σ τ : TypeExpr Var} :
      PropertyExpr Var τ → PropertyExpr Var (.sum σ τ)
  | lifted {σ : TypeExpr Var} :
      PropertyExpr Var σ → PropertyExpr Var (.lift σ)
  | box {σ : TypeExpr Var} :
      PropertyExpr Var σ → PropertyExpr Var (.plotkin σ)
  | diamond {σ : TypeExpr Var} :
      PropertyExpr Var σ → PropertyExpr Var (.plotkin σ)
  | recProp {X : Var} {σ τ : TypeExpr Var} :
      TypeExpr.RecUnfolding X σ τ →
        PropertyExpr Var τ → PropertyExpr Var (.recTy X σ)

/-- Finite disjunctions of properties, used by the decidability theorem's
normal-form package. -/
def PropertyExpr.finiteDisj {Var : Type u} {σ : TypeExpr Var} :
    List (PropertyExpr Var σ) → PropertyExpr Var σ
  | [] => PropertyExpr.falsity
  | φ :: rest => PropertyExpr.disj φ (PropertyExpr.finiteDisj rest)

/-- A structural size for property expressions.  This makes explicit the
"finitely many construction steps" used in the proof of Theorem 7.3.17. -/
def PropertyExpr.size {Var : Type u} : {σ : TypeExpr Var} → PropertyExpr Var σ → Nat
  | _, PropertyExpr.truth => 1
  | _, PropertyExpr.falsity => 1
  | _, PropertyExpr.conj φ ψ => 1 + PropertyExpr.size φ + PropertyExpr.size ψ
  | _, PropertyExpr.disj φ ψ => 1 + PropertyExpr.size φ + PropertyExpr.size ψ
  | _, PropertyExpr.arrow φ ψ => 1 + PropertyExpr.size φ + PropertyExpr.size ψ
  | _, PropertyExpr.product φ ψ => 1 + PropertyExpr.size φ + PropertyExpr.size ψ
  | _, PropertyExpr.sumLeft φ => 1 + PropertyExpr.size φ
  | _, PropertyExpr.sumRight ψ => 1 + PropertyExpr.size ψ
  | _, PropertyExpr.lifted φ => 1 + PropertyExpr.size φ
  | _, PropertyExpr.box φ => 1 + PropertyExpr.size φ
  | _, PropertyExpr.diamond φ => 1 + PropertyExpr.size φ
  | _, PropertyExpr.recProp _h φ => 1 + PropertyExpr.size φ

/-- Every property expression has a finite nonzero construction size. -/
theorem PropertyExpr.size_pos {Var : Type u} :
    ∀ {σ : TypeExpr Var}, (φ : PropertyExpr Var σ) → 0 < PropertyExpr.size φ
  | _, PropertyExpr.truth => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.falsity => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.conj φ ψ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.disj φ ψ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.arrow φ ψ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.product φ ψ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.sumLeft φ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.sumRight ψ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.lifted φ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.box φ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.diamond φ => by
      simp [PropertyExpr.size]
  | _, PropertyExpr.recProp _h φ => by
      simp [PropertyExpr.size]

/-- The distributive-lattice preorder rules displayed before Theorem 7.3.16,
recorded over the chosen carrier interpretation of formulas. -/
structure PropertyPreorderLatticeRules
    (σ : ClosedTypeExpr) (α : Type u) (le : α → α → Prop)
    (denote : PropertyExpr Empty σ → α) : Prop where
  refl : ∀ φ : PropertyExpr Empty σ, le (denote φ) (denote φ)
  trans :
    ∀ φ ψ χ : PropertyExpr Empty σ,
      le (denote φ) (denote ψ) → le (denote ψ) (denote χ) →
        le (denote φ) (denote χ)
  le_true :
    ∀ φ : PropertyExpr Empty σ,
      le (denote φ) (denote (PropertyExpr.truth : PropertyExpr Empty σ))
  conj_intro :
    ∀ φ ψ₁ ψ₂ : PropertyExpr Empty σ,
      le (denote φ) (denote ψ₁) → le (denote φ) (denote ψ₂) →
        le (denote φ) (denote (PropertyExpr.conj ψ₁ ψ₂))
  conj_left :
    ∀ φ ψ : PropertyExpr Empty σ,
      le (denote (PropertyExpr.conj φ ψ)) (denote φ)
  conj_right :
    ∀ φ ψ : PropertyExpr Empty σ,
      le (denote (PropertyExpr.conj φ ψ)) (denote ψ)
  false_le :
    ∀ φ : PropertyExpr Empty σ,
      le (denote (PropertyExpr.falsity : PropertyExpr Empty σ)) (denote φ)
  disj_elim :
    ∀ φ₁ φ₂ ψ : PropertyExpr Empty σ,
      le (denote φ₁) (denote ψ) → le (denote φ₂) (denote ψ) →
        le (denote (PropertyExpr.disj φ₁ φ₂)) (denote ψ)
  le_disj_left :
    ∀ φ ψ : PropertyExpr Empty σ,
      le (denote φ) (denote (PropertyExpr.disj φ ψ))
  le_disj_right :
    ∀ φ ψ : PropertyExpr Empty σ,
      le (denote ψ) (denote (PropertyExpr.disj φ ψ))
  distributivity :
    ∀ φ ψ χ : PropertyExpr Empty σ,
      le
        (denote (PropertyExpr.conj φ (PropertyExpr.disj ψ χ)))
        (denote
          (PropertyExpr.disj
            (PropertyExpr.conj φ ψ) (PropertyExpr.conj φ χ)))

/-- The syntactic domain prelocale `L(σ)` generated by the property language of a
closed type expression.  It records the formula-to-carrier interpretation and the
basic lattice clauses from the PDF's inductive rules. -/
structure PropertyLanguagePrelocale (σ : ClosedTypeExpr) where
  prelocale : DomainPrelocale.{u}
  denote : PropertyExpr Empty σ → prelocale.carrier
  truth_is_one :
    RelEquiv prelocale.le
      (denote (PropertyExpr.truth : PropertyExpr Empty σ)) prelocale.one
  falsity_is_zero :
    RelEquiv prelocale.le
      (denote (PropertyExpr.falsity : PropertyExpr Empty σ)) prelocale.zero
  conj_is_inf :
    ∀ φ ψ : PropertyExpr Empty σ,
      RelEquiv prelocale.le
        (denote (PropertyExpr.conj φ ψ)) (prelocale.inf (denote φ) (denote ψ))
  disj_is_sup :
    ∀ φ ψ : PropertyExpr Empty σ,
      RelEquiv prelocale.le
        (denote (PropertyExpr.disj φ ψ)) (prelocale.sup (denote φ) (denote ψ))
  generated_by_properties :
    ∀ a : prelocale.carrier,
      ∃ φ : PropertyExpr Empty σ, RelEquiv prelocale.le (denote φ) a
  preorder_lattice_rules :
    PropertyPreorderLatticeRules σ prelocale.carrier prelocale.le denote
  type_specific_preorder_rules : Prop
  compact_predicate_generated_by_rules : Prop
  termination_predicate_generated_by_rules : Prop

/-- Terms associated with type expressions.  The `typedVar` constructor
represents the denumerable set `V(σ)` of point variables for each closed or open
type expression; the other constructors mirror the term grammar displayed before
Theorem 7.3.18. -/
inductive TermExpr (Var : Type u) : TypeExpr Var → Type u where
  | bottom {σ : TypeExpr Var} : TermExpr Var σ
  | typedVar {σ : TypeExpr Var} : Nat → TermExpr Var σ
  | var (x : Var) : TermExpr Var (.var x)
  | lam {σ τ : TypeExpr Var} : TermExpr Var τ → TermExpr Var (.arr σ τ)
  | app {σ τ : TypeExpr Var} :
      TermExpr Var (.arr σ τ) → TermExpr Var σ → TermExpr Var τ
  | pair {σ τ : TypeExpr Var} :
      TermExpr Var σ → TermExpr Var τ → TermExpr Var (.prod σ τ)
  | letPair {σ τ ν : TypeExpr Var} :
      TermExpr Var (.prod σ τ) → TermExpr Var ν → TermExpr Var ν
  | inl {σ τ : TypeExpr Var} : TermExpr Var σ → TermExpr Var (.sum σ τ)
  | inr {σ τ : TypeExpr Var} : TermExpr Var τ → TermExpr Var (.sum σ τ)
  | caseSum {σ τ ν : TypeExpr Var} :
      TermExpr Var (.sum σ τ) → TermExpr Var ν → TermExpr Var ν → TermExpr Var ν
  | up {σ : TypeExpr Var} : TermExpr Var σ → TermExpr Var (.lift σ)
  | liftElim {σ τ : TypeExpr Var} :
      TermExpr Var (.lift σ) → TermExpr Var τ → TermExpr Var τ
  | singleton {σ : TypeExpr Var} : TermExpr Var σ → TermExpr Var (.plotkin σ)
  | over {σ τ : TypeExpr Var} :
      TermExpr Var (.plotkin σ) → TermExpr Var (.plotkin τ) →
        TermExpr Var (.plotkin τ)
  | union {σ : TypeExpr Var} :
      TermExpr Var (.plotkin σ) → TermExpr Var (.plotkin σ) → TermExpr Var (.plotkin σ)
  | tensor {σ τ : TypeExpr Var} :
      TermExpr Var (.plotkin σ) → TermExpr Var (.plotkin τ) →
        TermExpr Var (.plotkin (.prod σ τ))
  | fold {X : Var} {σ τ : TypeExpr Var} :
      TypeExpr.RecUnfolding X σ τ →
        TermExpr Var τ → TermExpr Var (.recTy X σ)
  | unfold {X : Var} {σ τ : TypeExpr Var} :
      TypeExpr.RecUnfolding X σ τ →
        TermExpr Var (.recTy X σ) → TermExpr Var τ
  | mu {σ : TypeExpr Var} : TermExpr Var σ → TermExpr Var σ

/-- A typed assumption in the property logic. -/
structure PropertyAssumption (Var : Type u) where
  σ : TypeExpr Var
  varName : Nat
  property : PropertyExpr Var σ

/-- Contexts contain at most one assumption for each variable, as in the PDF's
side condition on finite assumption lists. -/
def PropertyContextFunctional {Var : Type u}
    (Γ : List (PropertyAssumption Var)) : Prop :=
  ∀ a b : PropertyAssumption Var,
    a ∈ Γ → b ∈ Γ → a.σ = b.σ → a.varName = b.varName → a = b

/-- Sequents `Gamma |- M : phi`. -/
structure PropertySequent (Var : Type u) where
  context : List (PropertyAssumption Var)
  context_functional : PropertyContextFunctional context
  σ : TypeExpr Var
  term : TermExpr Var σ
  property : PropertyExpr Var σ

/-- Build a sequent from a context, a term, and a property of the term's type. -/
def PropertySequent.ofTerm {Var : Type u}
    (Γ : List (PropertyAssumption Var)) (hΓ : PropertyContextFunctional Γ)
    {σ : TypeExpr Var} (M : TermExpr Var σ) (φ : PropertyExpr Var σ) :
    PropertySequent Var where
  context := Γ
  context_functional := hΓ
  σ := σ
  term := M
  property := φ

/-- Change the goal property while keeping the context and term fixed. -/
def PropertySequent.withProperty {Var : Type u}
    (s : PropertySequent Var) (φ : PropertyExpr Var s.σ) :
    PropertySequent Var where
  context := s.context
  context_functional := s.context_functional
  σ := s.σ
  term := s.term
  property := φ

/-- Change the context while keeping the typed term and property fixed. -/
def PropertySequent.withContext {Var : Type u}
    (s : PropertySequent Var)
    (Γ : List (PropertyAssumption Var)) (hΓ : PropertyContextFunctional Γ) :
    PropertySequent Var where
  context := Γ
  context_functional := hΓ
  σ := s.σ
  term := s.term
  property := s.property

/-- The formula-preorder rules used by the property-logic sequent calculus. -/
inductive PropertyFormulaPreorder (Var : Type u) :
    {σ : TypeExpr Var} → PropertyExpr Var σ → PropertyExpr Var σ → Prop where
  | refl {σ : TypeExpr Var} (φ : PropertyExpr Var σ) :
      PropertyFormulaPreorder Var φ φ
  | trans {σ : TypeExpr Var} {φ ψ χ : PropertyExpr Var σ} :
      PropertyFormulaPreorder Var φ ψ →
        PropertyFormulaPreorder Var ψ χ →
          PropertyFormulaPreorder Var φ χ
  | le_true {σ : TypeExpr Var} (φ : PropertyExpr Var σ) :
      PropertyFormulaPreorder Var φ PropertyExpr.truth
  | false_le {σ : TypeExpr Var} (φ : PropertyExpr Var σ) :
      PropertyFormulaPreorder Var PropertyExpr.falsity φ
  | conj_intro {σ : TypeExpr Var} {φ ψ χ : PropertyExpr Var σ} :
      PropertyFormulaPreorder Var φ ψ →
        PropertyFormulaPreorder Var φ χ →
          PropertyFormulaPreorder Var φ (PropertyExpr.conj ψ χ)
  | conj_left {σ : TypeExpr Var} (φ ψ : PropertyExpr Var σ) :
      PropertyFormulaPreorder Var (PropertyExpr.conj φ ψ) φ
  | conj_right {σ : TypeExpr Var} (φ ψ : PropertyExpr Var σ) :
      PropertyFormulaPreorder Var (PropertyExpr.conj φ ψ) ψ
  | disj_elim {σ : TypeExpr Var} {φ ψ χ : PropertyExpr Var σ} :
      PropertyFormulaPreorder Var φ χ →
        PropertyFormulaPreorder Var ψ χ →
          PropertyFormulaPreorder Var (PropertyExpr.disj φ ψ) χ
  | le_disj_left {σ : TypeExpr Var} (φ ψ : PropertyExpr Var σ) :
      PropertyFormulaPreorder Var φ (PropertyExpr.disj φ ψ)
  | le_disj_right {σ : TypeExpr Var} (φ ψ : PropertyExpr Var σ) :
      PropertyFormulaPreorder Var ψ (PropertyExpr.disj φ ψ)
  | distributivity {σ : TypeExpr Var} (φ ψ χ : PropertyExpr Var σ) :
      PropertyFormulaPreorder Var
        (PropertyExpr.conj φ (PropertyExpr.disj ψ χ))
        (PropertyExpr.disj (PropertyExpr.conj φ ψ) (PropertyExpr.conj φ χ))

/-- Conjunction is monotone for the generated formula preorder. -/
theorem PropertyFormulaPreorder.conj_mono {Var : Type u} {σ : TypeExpr Var}
    {φ φ' ψ ψ' : PropertyExpr Var σ}
    (hφ : PropertyFormulaPreorder Var φ φ')
    (hψ : PropertyFormulaPreorder Var ψ ψ') :
    PropertyFormulaPreorder Var
      (PropertyExpr.conj φ ψ) (PropertyExpr.conj φ' ψ') := by
  exact
    PropertyFormulaPreorder.conj_intro
      (PropertyFormulaPreorder.trans
        (PropertyFormulaPreorder.conj_left φ ψ) hφ)
      (PropertyFormulaPreorder.trans
        (PropertyFormulaPreorder.conj_right φ ψ) hψ)

/-- Disjunction is monotone for the generated formula preorder. -/
theorem PropertyFormulaPreorder.disj_mono {Var : Type u} {σ : TypeExpr Var}
    {φ φ' ψ ψ' : PropertyExpr Var σ}
    (hφ : PropertyFormulaPreorder Var φ φ')
    (hψ : PropertyFormulaPreorder Var ψ ψ') :
    PropertyFormulaPreorder Var
      (PropertyExpr.disj φ ψ) (PropertyExpr.disj φ' ψ') := by
  exact
    PropertyFormulaPreorder.disj_elim
      (PropertyFormulaPreorder.trans hφ
        (PropertyFormulaPreorder.le_disj_left φ' ψ'))
      (PropertyFormulaPreorder.trans hψ
        (PropertyFormulaPreorder.le_disj_right φ' ψ'))

/-- Conjunction is commutative up to the generated formula preorder. -/
theorem PropertyFormulaPreorder.conj_comm {Var : Type u} {σ : TypeExpr Var}
    (φ ψ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.conj φ ψ) (PropertyExpr.conj ψ φ) := by
  exact
    PropertyFormulaPreorder.conj_intro
      (PropertyFormulaPreorder.conj_right φ ψ)
      (PropertyFormulaPreorder.conj_left φ ψ)

/-- Disjunction is commutative up to the generated formula preorder. -/
theorem PropertyFormulaPreorder.disj_comm {Var : Type u} {σ : TypeExpr Var}
    (φ ψ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.disj φ ψ) (PropertyExpr.disj ψ φ) := by
  exact
    PropertyFormulaPreorder.disj_elim
      (PropertyFormulaPreorder.le_disj_right ψ φ)
      (PropertyFormulaPreorder.le_disj_left ψ φ)

/-- Every listed formula is below its finite disjunction. -/
theorem PropertyFormulaPreorder.le_finiteDisj_of_mem {Var : Type u}
    {σ : TypeExpr Var} {φ : PropertyExpr Var σ} {l : List (PropertyExpr Var σ)}
    (hmem : φ ∈ l) :
    PropertyFormulaPreorder Var φ (PropertyExpr.finiteDisj l) := by
  induction l with
  | nil =>
      cases hmem
  | cons head rest ih =>
      simp only [List.mem_cons] at hmem
      change
        PropertyFormulaPreorder Var φ
          (PropertyExpr.disj head (PropertyExpr.finiteDisj rest))
      rcases hmem with hφ | hmem
      · cases hφ
        exact PropertyFormulaPreorder.le_disj_left φ (PropertyExpr.finiteDisj rest)
      · exact
          PropertyFormulaPreorder.trans (ih hmem)
            (PropertyFormulaPreorder.le_disj_right head (PropertyExpr.finiteDisj rest))

/-- A finite disjunction is below a formula if every listed disjunct is below it. -/
theorem PropertyFormulaPreorder.finiteDisj_le {Var : Type u}
    {σ : TypeExpr Var} {l : List (PropertyExpr Var σ)} {ψ : PropertyExpr Var σ}
    (h : ∀ φ : PropertyExpr Var σ, φ ∈ l → PropertyFormulaPreorder Var φ ψ) :
    PropertyFormulaPreorder Var (PropertyExpr.finiteDisj l) ψ := by
  induction l with
  | nil =>
      exact PropertyFormulaPreorder.false_le ψ
  | cons φ rest ih =>
      simp only [PropertyExpr.finiteDisj]
      refine PropertyFormulaPreorder.disj_elim (h φ ?_) ?_
      · simp
      · exact ih (by
          intro χ hχ
          exact h χ (by simp [hχ]))

/-- Formula filters over a fixed type in the property-language preorder. -/
structure PropertyFormulaFilter (Var : Type u) {σ : TypeExpr Var}
    (F : Set (PropertyExpr Var σ)) : Prop where
  truth_mem : (PropertyExpr.truth : PropertyExpr Var σ) ∈ F
  upward_closed :
    ∀ ⦃φ ψ : PropertyExpr Var σ⦄,
      φ ∈ F → PropertyFormulaPreorder Var φ ψ → ψ ∈ F
  conj_closed :
    ∀ ⦃φ ψ : PropertyExpr Var σ⦄,
      φ ∈ F → ψ ∈ F → PropertyExpr.conj φ ψ ∈ F

/-- Prime formula filters add properness and disjunction primality. -/
structure PropertyFormulaPrimeFilter (Var : Type u) {σ : TypeExpr Var}
    (F : Set (PropertyExpr Var σ)) : Prop
    extends PropertyFormulaFilter Var F where
  false_not_mem : (PropertyExpr.falsity : PropertyExpr Var σ) ∉ F
  disj_prime :
    ∀ ⦃φ ψ : PropertyExpr Var σ⦄,
      PropertyExpr.disj φ ψ ∈ F → φ ∈ F ∨ ψ ∈ F

/-- A property assumption is prime when its formula is join-prime in the
formula preorder for its type. -/
def PropertyAssumption.IsPrime {Var : Type u} (a : PropertyAssumption Var) :
    Prop :=
  ∀ ψ χ : PropertyExpr Var a.σ,
    PropertyFormulaPreorder Var a.property (PropertyExpr.disj ψ χ) →
      PropertyFormulaPreorder Var a.property ψ ∨
        PropertyFormulaPreorder Var a.property χ

/-- Prime contexts satisfy the finite-context functionality side condition and
carry only prime property assumptions. -/
def PropertyContextPrime {Var : Type u}
    (Γ : List (PropertyAssumption Var)) : Prop :=
  PropertyContextFunctional Γ ∧
    ∀ a : PropertyAssumption Var, a ∈ Γ → a.IsPrime

/-- Formula filters contain a conjunction exactly when they contain both
conjuncts. -/
theorem PropertyFormulaFilter.conj_mem_iff {Var : Type u} {σ : TypeExpr Var}
    {F : Set (PropertyExpr Var σ)} (hF : PropertyFormulaFilter Var F)
    (φ ψ : PropertyExpr Var σ) :
    PropertyExpr.conj φ ψ ∈ F ↔ φ ∈ F ∧ ψ ∈ F := by
  constructor
  · intro h
    exact
      ⟨hF.upward_closed h (PropertyFormulaPreorder.conj_left φ ψ),
        hF.upward_closed h (PropertyFormulaPreorder.conj_right φ ψ)⟩
  · intro h
    exact hF.conj_closed h.1 h.2

/-- A formula filter contains a finite disjunction whenever it contains one of
the listed disjuncts. -/
theorem PropertyFormulaFilter.finiteDisj_mem_of_mem {Var : Type u}
    {σ : TypeExpr Var} {F : Set (PropertyExpr Var σ)}
    (hF : PropertyFormulaFilter Var F)
    {l : List (PropertyExpr Var σ)} {φ : PropertyExpr Var σ}
    (hmem : φ ∈ l) (hφ : φ ∈ F) :
    PropertyExpr.finiteDisj l ∈ F :=
  hF.upward_closed hφ (PropertyFormulaPreorder.le_finiteDisj_of_mem hmem)

/-- Prime formula filters contain a disjunction exactly when they contain one of
the disjuncts. -/
theorem PropertyFormulaPrimeFilter.disj_mem_iff {Var : Type u} {σ : TypeExpr Var}
    {F : Set (PropertyExpr Var σ)} (hF : PropertyFormulaPrimeFilter Var F)
    (φ ψ : PropertyExpr Var σ) :
    PropertyExpr.disj φ ψ ∈ F ↔ φ ∈ F ∨ ψ ∈ F := by
  constructor
  · intro h
    exact hF.disj_prime h
  · intro h
    rcases h with hφ | hψ
    · exact hF.upward_closed hφ (PropertyFormulaPreorder.le_disj_left φ ψ)
    · exact hF.upward_closed hψ (PropertyFormulaPreorder.le_disj_right φ ψ)

/-- Prime formula filters contain a finite disjunction exactly when they contain
one of the listed disjuncts. -/
theorem PropertyFormulaPrimeFilter.finiteDisj_mem_iff {Var : Type u}
    {σ : TypeExpr Var} {F : Set (PropertyExpr Var σ)}
    (hF : PropertyFormulaPrimeFilter Var F)
    (l : List (PropertyExpr Var σ)) :
    PropertyExpr.finiteDisj l ∈ F ↔ ∃ φ : PropertyExpr Var σ, φ ∈ l ∧ φ ∈ F := by
  induction l with
  | nil =>
      constructor
      · intro h
        exact False.elim (hF.false_not_mem h)
      · intro h
        rcases h with ⟨φ, hmem, _hφ⟩
        cases hmem
  | cons φ rest ih =>
      constructor
      · intro h
        have hdisj :
            PropertyExpr.disj φ (PropertyExpr.finiteDisj rest) ∈ F := by
          simpa [PropertyExpr.finiteDisj] using h
        rcases (PropertyFormulaPrimeFilter.disj_mem_iff hF φ
            (PropertyExpr.finiteDisj rest)).1 hdisj with hφ | hrest
        · exact ⟨φ, by simp, hφ⟩
        · rcases ih.1 hrest with ⟨ψ, hψmem, hψ⟩
          exact ⟨ψ, by simp [hψmem], hψ⟩
      · intro h
        rcases h with ⟨ψ, hψmem, hψ⟩
        exact
          hF.toPropertyFormulaFilter.finiteDisj_mem_of_mem
            (by simpa using hψmem) hψ

/-- Prime contexts are functional contexts. -/
theorem PropertyContextPrime.functional {Var : Type u}
    {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextPrime Γ) :
    PropertyContextFunctional Γ :=
  hΓ.1

/-- Every assumption in a prime context has a prime formula. -/
theorem PropertyContextPrime.assumption_prime {Var : Type u}
    {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextPrime Γ)
    {a : PropertyAssumption Var} (ha : a ∈ Γ) :
    a.IsPrime :=
  hΓ.2 a ha

/-- The empty context is functional. -/
theorem PropertyContextFunctional.nil {Var : Type u} :
    PropertyContextFunctional ([] : List (PropertyAssumption Var)) := by
  intro a _b ha _hb _hσ _hvar
  cases ha

/-- Functionality is inherited by subcontexts. -/
theorem PropertyContextFunctional.subset {Var : Type u}
    {Γ Δ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
    (hsub : ∀ a : PropertyAssumption Var, a ∈ Δ → a ∈ Γ) :
    PropertyContextFunctional Δ := by
  intro a b ha hb hσ hvar
  exact hΓ a b (hsub a ha) (hsub b hb) hσ hvar

/-- A fresh assumption can be consed onto a functional context. -/
theorem PropertyContextFunctional.cons {Var : Type u}
    {Γ : List (PropertyAssumption Var)} {a : PropertyAssumption Var}
    (hΓ : PropertyContextFunctional Γ)
    (hfresh :
      ∀ b : PropertyAssumption Var, b ∈ Γ →
        a.σ = b.σ → a.varName = b.varName → False) :
    PropertyContextFunctional (a :: Γ) := by
  intro x y hx hy hσ hvar
  simp only [List.mem_cons] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · rfl
    · exact False.elim (hfresh y hy hσ hvar)
  · rcases hy with rfl | hy
    · exact False.elim (hfresh x hx hσ.symm hvar.symm)
    · exact hΓ x y hx hy hσ hvar

/-- The empty context is prime. -/
theorem PropertyContextPrime.nil {Var : Type u} :
    PropertyContextPrime ([] : List (PropertyAssumption Var)) := by
  constructor
  · exact PropertyContextFunctional.nil
  · intro a ha
    cases ha

/-- Primality is inherited by subcontexts. -/
theorem PropertyContextPrime.subset {Var : Type u}
    {Γ Δ : List (PropertyAssumption Var)} (hΓ : PropertyContextPrime Γ)
    (hsub : ∀ a : PropertyAssumption Var, a ∈ Δ → a ∈ Γ) :
    PropertyContextPrime Δ := by
  constructor
  · exact PropertyContextFunctional.subset hΓ.1 hsub
  · intro a ha
    exact hΓ.2 a (hsub a ha)

/-- A fresh prime assumption can be consed onto a prime context. -/
theorem PropertyContextPrime.cons {Var : Type u}
    {Γ : List (PropertyAssumption Var)} {a : PropertyAssumption Var}
    (hΓ : PropertyContextPrime Γ) (ha : a.IsPrime)
    (hfresh :
      ∀ b : PropertyAssumption Var, b ∈ Γ →
        a.σ = b.σ → a.varName = b.varName → False) :
    PropertyContextPrime (a :: Γ) := by
  constructor
  · exact PropertyContextFunctional.cons hΓ.1 hfresh
  · intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ha
    · exact hΓ.2 b hb

/-- The tail of a functional cons context is functional. -/
theorem PropertyContextFunctional.tail {Var : Type u}
    {Γ : List (PropertyAssumption Var)} {a : PropertyAssumption Var}
    (hΓ : PropertyContextFunctional (a :: Γ)) :
    PropertyContextFunctional Γ := by
  exact
    PropertyContextFunctional.subset hΓ
      (by
        intro b hb
        simp [hb])

/-- In a functional cons context, a tail assumption with the head variable is
equal to the head assumption. -/
theorem PropertyContextFunctional.head_eq_of_same_var {Var : Type u}
    {Γ : List (PropertyAssumption Var)} {a b : PropertyAssumption Var}
    (hΓ : PropertyContextFunctional (a :: Γ)) (hb : b ∈ Γ)
    (hσ : a.σ = b.σ) (hvar : a.varName = b.varName) :
    a = b := by
  exact hΓ a b (by simp) (by simp [hb]) hσ hvar

/-- The head assumption of a prime cons context is prime. -/
theorem PropertyContextPrime.head_prime {Var : Type u}
    {Γ : List (PropertyAssumption Var)} {a : PropertyAssumption Var}
    (hΓ : PropertyContextPrime (a :: Γ)) :
    a.IsPrime := by
  exact hΓ.2 a (by simp)

/-- The tail of a prime cons context is prime. -/
theorem PropertyContextPrime.tail {Var : Type u}
    {Γ : List (PropertyAssumption Var)} {a : PropertyAssumption Var}
    (hΓ : PropertyContextPrime (a :: Γ)) :
    PropertyContextPrime Γ := by
  exact
    PropertyContextPrime.subset hΓ
      (by
        intro b hb
        simp [hb])

/-- In a prime cons context, a tail assumption with the head variable is equal
to the head assumption. -/
theorem PropertyContextPrime.head_eq_of_same_var {Var : Type u}
    {Γ : List (PropertyAssumption Var)} {a b : PropertyAssumption Var}
    (hΓ : PropertyContextPrime (a :: Γ)) (hb : b ∈ Γ)
    (hσ : a.σ = b.σ) (hvar : a.varName = b.varName) :
    a = b := by
  exact PropertyContextFunctional.head_eq_of_same_var hΓ.1 hb hσ hvar

/-- Explicit derivation syntax for the main displayed domain-logic rules.  This
records the rule shapes separately from the semantic soundness/completeness
package below. -/
inductive DomainLogicDerivation (Var : Type u) : PropertySequent Var → Prop where
  | truth
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} (M : TermExpr Var σ) :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.truth : PropertyExpr Var σ))
  | variable
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      (a : PropertyAssumption Var) (_ha : a ∈ Γ) :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ
          (TermExpr.typedVar (σ := a.σ) a.varName) a.property)
  | bottom
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ (TermExpr.bottom : TermExpr Var σ)
          (PropertyExpr.truth : PropertyExpr Var σ))
  | structural_weakening {s : PropertySequent Var}
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ) :
      (∀ a : PropertyAssumption Var, a ∈ s.context → a ∈ Γ) →
        DomainLogicDerivation Var s →
          DomainLogicDerivation Var (PropertySequent.withContext s Γ hΓ)
  | preorder {s : PropertySequent Var} {ψ : PropertyExpr Var s.σ} :
      DomainLogicDerivation Var s →
        PropertyFormulaPreorder Var s.property ψ →
          DomainLogicDerivation Var (PropertySequent.withProperty s ψ)
  | conj_intro {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ} :
      DomainLogicDerivation Var (PropertySequent.withProperty s φ) →
        DomainLogicDerivation Var (PropertySequent.withProperty s ψ) →
          DomainLogicDerivation Var
            (PropertySequent.withProperty s (PropertyExpr.conj φ ψ))
  | disj_left {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ} :
      DomainLogicDerivation Var (PropertySequent.withProperty s φ) →
        DomainLogicDerivation Var
          (PropertySequent.withProperty s (PropertyExpr.disj φ ψ))
  | disj_right {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ} :
      DomainLogicDerivation Var (PropertySequent.withProperty s ψ) →
        DomainLogicDerivation Var
          (PropertySequent.withProperty s (PropertyExpr.disj φ ψ))
  | lam
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var} {M : TermExpr Var τ}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M ψ) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ (TermExpr.lam (σ := σ) M)
            (PropertyExpr.arrow φ ψ))
  | app
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var} {M : TermExpr Var (.arr σ τ)} {N : TermExpr Var σ}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.arrow φ ψ)) →
        DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ N φ) →
          DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ (TermExpr.app M N) ψ)
  | pair
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var} {M : TermExpr Var σ} {N : TermExpr Var τ}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M φ) →
        DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ N ψ) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.pair M N)
              (PropertyExpr.product φ ψ))
  | let_pair
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ ν : TypeExpr Var}
      {M : TermExpr Var (.prod σ τ)} {N : TermExpr Var ν}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ}
      {χ : PropertyExpr Var ν} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.product φ ψ)) →
        DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ N χ) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.letPair M N) χ)
  | inl
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var} {M : TermExpr Var σ} {φ : PropertyExpr Var σ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M φ) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ (TermExpr.inl (τ := τ) M)
            (PropertyExpr.sumLeft (τ := τ) φ))
  | inr
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var} {M : TermExpr Var τ} {φ : PropertyExpr Var τ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M φ) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ (TermExpr.inr (σ := σ) M)
            (PropertyExpr.sumRight (σ := σ) φ))
  | case_sum
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ ν : TypeExpr Var}
      {M : TermExpr Var (.sum σ τ)} {N P : TermExpr Var ν}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ}
      {χ : PropertyExpr Var ν} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M
          (PropertyExpr.disj
            (PropertyExpr.sumLeft (τ := τ) φ)
            (PropertyExpr.sumRight (σ := σ) ψ))) →
        DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ N χ) →
        DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ P χ) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.caseSum M N P) χ)
  | up
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} {M : TermExpr Var σ} {φ : PropertyExpr Var σ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M φ) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ (TermExpr.up M) (PropertyExpr.lifted φ))
  | lift_elim
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var} {M : TermExpr Var (.lift σ)} {N : TermExpr Var τ}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.lifted φ)) →
        DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ N ψ) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.liftElim M N) ψ)
  | singleton_box
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} {M : TermExpr Var σ} {φ : PropertyExpr Var σ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M φ) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ (TermExpr.singleton M) (PropertyExpr.box φ))
  | singleton_diamond
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} {M : TermExpr Var σ} {φ : PropertyExpr Var σ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M φ) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ (TermExpr.singleton M) (PropertyExpr.diamond φ))
  | over_box
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var}
      {M : TermExpr Var (.plotkin σ)} {N : TermExpr Var (.plotkin τ)}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.diamond φ)) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ N (PropertyExpr.box ψ)) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.over M N) (PropertyExpr.box ψ))
  | over_diamond
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var}
      {M : TermExpr Var (.plotkin σ)} {N : TermExpr Var (.plotkin τ)}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.diamond φ)) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ N (PropertyExpr.diamond ψ)) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.over M N) (PropertyExpr.diamond ψ))
  | union_box
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} {M N : TermExpr Var (.plotkin σ)}
      {φ : PropertyExpr Var σ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.box φ)) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ N (PropertyExpr.box φ)) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.union M N) (PropertyExpr.box φ))
  | union_diamond_left
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} {M N : TermExpr Var (.plotkin σ)}
      {φ : PropertyExpr Var σ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.diamond φ)) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.union M N) (PropertyExpr.diamond φ))
  | union_diamond_right
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} {M N : TermExpr Var (.plotkin σ)}
      {φ : PropertyExpr Var σ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ N (PropertyExpr.diamond φ)) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.union M N) (PropertyExpr.diamond φ))
  | tensor_box
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var}
      {M : TermExpr Var (.plotkin σ)} {N : TermExpr Var (.plotkin τ)}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.box φ)) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ N (PropertyExpr.box ψ)) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.tensor M N)
              (PropertyExpr.box (PropertyExpr.product φ ψ)))
  | tensor_diamond
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ τ : TypeExpr Var}
      {M : TermExpr Var (.plotkin σ)} {N : TermExpr Var (.plotkin τ)}
      {φ : PropertyExpr Var σ} {ψ : PropertyExpr Var τ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.diamond φ)) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ N (PropertyExpr.diamond ψ)) →
          DomainLogicDerivation Var
            (PropertySequent.ofTerm Γ hΓ (TermExpr.tensor M N)
              (PropertyExpr.diamond (PropertyExpr.product φ ψ)))
  | fold
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {X : Var} {σ τ : TypeExpr Var} {hrec : TypeExpr.RecUnfolding X σ τ}
      {M : TermExpr Var τ} {φ : PropertyExpr Var τ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M φ) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ (TermExpr.fold hrec M)
            (PropertyExpr.recProp hrec φ))
  | unfold
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {X : Var} {σ τ : TypeExpr Var} {hrec : TypeExpr.RecUnfolding X σ τ}
      {M : TermExpr Var (.recTy X σ)} {φ : PropertyExpr Var τ} :
      DomainLogicDerivation Var
        (PropertySequent.ofTerm Γ hΓ M (PropertyExpr.recProp hrec φ)) →
        DomainLogicDerivation Var
          (PropertySequent.ofTerm Γ hΓ (TermExpr.unfold hrec M) φ)
  | fixpoint
      {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
      {σ : TypeExpr Var} {M : TermExpr Var σ} {φ : PropertyExpr Var σ} :
      DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ M φ) →
        DomainLogicDerivation Var (PropertySequent.ofTerm Γ hΓ (TermExpr.mu M) φ)

/-- Derived form of structural weakening for an arbitrary supercontext. -/
theorem DomainLogicDerivation.weaken_context {Var : Type u}
    {s : PropertySequent Var}
    {Γ : List (PropertyAssumption Var)} (hΓ : PropertyContextFunctional Γ)
    (hsub : ∀ a : PropertyAssumption Var, a ∈ s.context → a ∈ Γ) :
    DomainLogicDerivation Var s →
      DomainLogicDerivation Var (PropertySequent.withContext s Γ hΓ) := by
  intro hs
  exact DomainLogicDerivation.structural_weakening hΓ hsub hs

/-- Derived weakening that extends a sequent by one fresh assumption. -/
theorem DomainLogicDerivation.weaken_cons {Var : Type u}
    {s : PropertySequent Var} {a : PropertyAssumption Var}
    (hfresh :
      ∀ b : PropertyAssumption Var, b ∈ s.context →
        a.σ = b.σ → a.varName = b.varName → False) :
    DomainLogicDerivation Var s →
      DomainLogicDerivation Var
        (PropertySequent.withContext s (a :: s.context)
          (PropertyContextFunctional.cons s.context_functional hfresh)) := by
  intro hs
  exact
    DomainLogicDerivation.weaken_context
      (PropertyContextFunctional.cons s.context_functional hfresh)
      (by
        intro b hb
        simp [hb]) hs

/-- Derived conjunction introduction after formula-preorder weakening of each
conjunct. -/
theorem DomainLogicDerivation.conj_intro_preorder {Var : Type u}
    {s : PropertySequent Var} {φ φ' ψ ψ' : PropertyExpr Var s.σ}
    (hφ : DomainLogicDerivation Var (PropertySequent.withProperty s φ))
    (hψ : DomainLogicDerivation Var (PropertySequent.withProperty s ψ))
    (hφ' : PropertyFormulaPreorder Var φ φ')
    (hψ' : PropertyFormulaPreorder Var ψ ψ') :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj φ' ψ')) := by
  have dφ' :
      DomainLogicDerivation Var (PropertySequent.withProperty s φ') := by
    simpa [PropertySequent.withProperty] using
      (DomainLogicDerivation.preorder hφ hφ')
  have dψ' :
      DomainLogicDerivation Var (PropertySequent.withProperty s ψ') := by
    simpa [PropertySequent.withProperty] using
      (DomainLogicDerivation.preorder hψ hψ')
  exact DomainLogicDerivation.conj_intro dφ' dψ'

/-- Derived transport across commutativity of conjunction. -/
theorem DomainLogicDerivation.conj_comm {Var : Type u}
    {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj φ ψ))) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj ψ φ)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h (PropertyFormulaPreorder.conj_comm φ ψ))

/-- Derived transport across commutativity of disjunction. -/
theorem DomainLogicDerivation.disj_comm {Var : Type u}
    {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj φ ψ))) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj ψ φ)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h (PropertyFormulaPreorder.disj_comm φ ψ))

/-- A derivation of one listed disjunct derives the finite disjunction. -/
theorem DomainLogicDerivation.finiteDisj_of_mem {Var : Type u}
    {s : PropertySequent Var} {l : List (PropertyExpr Var s.σ)}
    {φ : PropertyExpr Var s.σ}
    (hmem : φ ∈ l)
    (hφ : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.finiteDisj l)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder hφ
      (PropertyFormulaPreorder.le_finiteDisj_of_mem hmem))

/-- A finite-disjunction derivation can be eliminated along a formula-preorder
upper bound for every listed disjunct. -/
theorem DomainLogicDerivation.finiteDisj_elim_preorder {Var : Type u}
    {s : PropertySequent Var} {l : List (PropertyExpr Var s.σ)}
    {ψ : PropertyExpr Var s.σ}
    (hl : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.finiteDisj l)))
    (hψ : ∀ φ : PropertyExpr Var s.σ,
      φ ∈ l → PropertyFormulaPreorder Var φ ψ) :
    DomainLogicDerivation Var (PropertySequent.withProperty s ψ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder hl
      (PropertyFormulaPreorder.finiteDisj_le hψ))

/-- Derived transitive formula-preorder transport for a fixed sequent. -/
theorem DomainLogicDerivation.preorder_trans {Var : Type u}
    {s : PropertySequent Var} {φ ψ χ : PropertyExpr Var s.σ}
    (hφ : DomainLogicDerivation Var (PropertySequent.withProperty s φ))
    (hφψ : PropertyFormulaPreorder Var φ ψ)
    (hψχ : PropertyFormulaPreorder Var ψ χ) :
    DomainLogicDerivation Var (PropertySequent.withProperty s χ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder hφ
      (PropertyFormulaPreorder.trans hφψ hψχ))

/-- Derived conjunction-left elimination for displayed derivations. -/
theorem DomainLogicDerivation.conj_left {Var : Type u}
    {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj φ ψ))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.conj_left φ ψ))

/-- Derived conjunction-right elimination for displayed derivations. -/
theorem DomainLogicDerivation.conj_right {Var : Type u}
    {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj φ ψ))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s ψ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.conj_right φ ψ))

/-- Derived left disjunction introduction after formula-preorder weakening. -/
theorem DomainLogicDerivation.disj_left_preorder {Var : Type u}
    {s : PropertySequent Var} {φ φ' ψ : PropertyExpr Var s.σ}
    (hφ : DomainLogicDerivation Var (PropertySequent.withProperty s φ))
    (hφ' : PropertyFormulaPreorder Var φ φ') :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj φ' ψ)) := by
  exact
    DomainLogicDerivation.preorder_trans hφ hφ'
      (PropertyFormulaPreorder.le_disj_left φ' ψ)

/-- Derived right disjunction introduction after formula-preorder weakening. -/
theorem DomainLogicDerivation.disj_right_preorder {Var : Type u}
    {s : PropertySequent Var} {φ ψ ψ' : PropertyExpr Var s.σ}
    (hψ : DomainLogicDerivation Var (PropertySequent.withProperty s ψ))
    (hψ' : PropertyFormulaPreorder Var ψ ψ') :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj φ ψ')) := by
  exact
    DomainLogicDerivation.preorder_trans hψ hψ'
      (PropertyFormulaPreorder.le_disj_right φ ψ')

/-- Truth is derivable for any displayed sequent shape with the same context
and term. -/
theorem DomainLogicDerivation.truth_intro {Var : Type u}
    (s : PropertySequent Var) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.truth : PropertyExpr Var s.σ)) := by
  simpa [PropertySequent.withProperty, PropertySequent.ofTerm] using
    (DomainLogicDerivation.truth s.context_functional s.term)

/-- Falsity entails every formula in the displayed derivation preorder. -/
theorem DomainLogicDerivation.false_elim {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (hfalse : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.falsity : PropertyExpr Var s.σ))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder hfalse
      (PropertyFormulaPreorder.false_le φ))

/-- Derived conjunction monotonicity for displayed derivations. -/
theorem DomainLogicDerivation.conj_mono {Var : Type u}
    {s : PropertySequent Var} {φ φ' ψ ψ' : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj φ ψ)))
    (hφ : PropertyFormulaPreorder Var φ φ')
    (hψ : PropertyFormulaPreorder Var ψ ψ') :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj φ' ψ')) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.conj_mono hφ hψ))

/-- Derived disjunction monotonicity for displayed derivations. -/
theorem DomainLogicDerivation.disj_mono {Var : Type u}
    {s : PropertySequent Var} {φ φ' ψ ψ' : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj φ ψ)))
    (hφ : PropertyFormulaPreorder Var φ φ')
    (hψ : PropertyFormulaPreorder Var ψ ψ') :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj φ' ψ')) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.disj_mono hφ hψ))

/-- Derived binary disjunction elimination along a common formula-preorder
upper bound. -/
theorem DomainLogicDerivation.disj_elim_preorder {Var : Type u}
    {s : PropertySequent Var} {φ ψ χ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj φ ψ)))
    (hφ : PropertyFormulaPreorder Var φ χ)
    (hψ : PropertyFormulaPreorder Var ψ χ) :
    DomainLogicDerivation Var (PropertySequent.withProperty s χ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.disj_elim hφ hψ))

/-- Derived distributivity transport for displayed derivations. -/
theorem DomainLogicDerivation.distributivity {Var : Type u}
    {s : PropertySequent Var} {φ ψ χ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj φ (PropertyExpr.disj ψ χ)))) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj (PropertyExpr.conj φ ψ)
          (PropertyExpr.conj φ χ))) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.distributivity φ ψ χ))

/-- Conjunction is associative in the generated formula preorder. -/
theorem PropertyFormulaPreorder.conj_assoc {Var : Type u} {σ : TypeExpr Var}
    (φ ψ χ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.conj (PropertyExpr.conj φ ψ) χ)
      (PropertyExpr.conj φ (PropertyExpr.conj ψ χ)) := by
  exact
    PropertyFormulaPreorder.conj_intro
      (PropertyFormulaPreorder.trans
        (PropertyFormulaPreorder.conj_left (PropertyExpr.conj φ ψ) χ)
        (PropertyFormulaPreorder.conj_left φ ψ))
      (PropertyFormulaPreorder.conj_intro
        (PropertyFormulaPreorder.trans
          (PropertyFormulaPreorder.conj_left (PropertyExpr.conj φ ψ) χ)
          (PropertyFormulaPreorder.conj_right φ ψ))
        (PropertyFormulaPreorder.conj_right (PropertyExpr.conj φ ψ) χ))

/-- Conjunction associativity in the reverse generated-preorder direction. -/
theorem PropertyFormulaPreorder.conj_assoc_symm {Var : Type u}
    {σ : TypeExpr Var} (φ ψ χ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.conj φ (PropertyExpr.conj ψ χ))
      (PropertyExpr.conj (PropertyExpr.conj φ ψ) χ) := by
  exact
    PropertyFormulaPreorder.conj_intro
      (PropertyFormulaPreorder.conj_intro
        (PropertyFormulaPreorder.conj_left φ (PropertyExpr.conj ψ χ))
        (PropertyFormulaPreorder.trans
          (PropertyFormulaPreorder.conj_right φ (PropertyExpr.conj ψ χ))
          (PropertyFormulaPreorder.conj_left ψ χ)))
      (PropertyFormulaPreorder.trans
        (PropertyFormulaPreorder.conj_right φ (PropertyExpr.conj ψ χ))
        (PropertyFormulaPreorder.conj_right ψ χ))

/-- Disjunction is associative in the generated formula preorder. -/
theorem PropertyFormulaPreorder.disj_assoc {Var : Type u} {σ : TypeExpr Var}
    (φ ψ χ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.disj (PropertyExpr.disj φ ψ) χ)
      (PropertyExpr.disj φ (PropertyExpr.disj ψ χ)) := by
  exact
    PropertyFormulaPreorder.disj_elim
      (PropertyFormulaPreorder.disj_elim
        (PropertyFormulaPreorder.le_disj_left φ (PropertyExpr.disj ψ χ))
        (PropertyFormulaPreorder.trans
          (PropertyFormulaPreorder.le_disj_left ψ χ)
          (PropertyFormulaPreorder.le_disj_right φ (PropertyExpr.disj ψ χ))))
      (PropertyFormulaPreorder.trans
        (PropertyFormulaPreorder.le_disj_right ψ χ)
        (PropertyFormulaPreorder.le_disj_right φ (PropertyExpr.disj ψ χ)))

/-- Disjunction associativity in the reverse generated-preorder direction. -/
theorem PropertyFormulaPreorder.disj_assoc_symm {Var : Type u}
    {σ : TypeExpr Var} (φ ψ χ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.disj φ (PropertyExpr.disj ψ χ))
      (PropertyExpr.disj (PropertyExpr.disj φ ψ) χ) := by
  exact
    PropertyFormulaPreorder.disj_elim
      (PropertyFormulaPreorder.trans
        (PropertyFormulaPreorder.le_disj_left φ ψ)
        (PropertyFormulaPreorder.le_disj_left (PropertyExpr.disj φ ψ) χ))
      (PropertyFormulaPreorder.disj_elim
        (PropertyFormulaPreorder.trans
          (PropertyFormulaPreorder.le_disj_right φ ψ)
          (PropertyFormulaPreorder.le_disj_left (PropertyExpr.disj φ ψ) χ))
        (PropertyFormulaPreorder.le_disj_right (PropertyExpr.disj φ ψ) χ))

/-- Conjunction idempotence in the generated formula preorder. -/
theorem PropertyFormulaPreorder.conj_idem {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var (PropertyExpr.conj φ φ) φ := by
  exact PropertyFormulaPreorder.conj_left φ φ

/-- A formula is below its self-conjunction in the generated formula preorder. -/
theorem PropertyFormulaPreorder.le_conj_self {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var φ (PropertyExpr.conj φ φ) := by
  exact
    PropertyFormulaPreorder.conj_intro
      (PropertyFormulaPreorder.refl φ) (PropertyFormulaPreorder.refl φ)

/-- Disjunction idempotence in the generated formula preorder. -/
theorem PropertyFormulaPreorder.disj_idem {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var (PropertyExpr.disj φ φ) φ := by
  exact
    PropertyFormulaPreorder.disj_elim
      (PropertyFormulaPreorder.refl φ) (PropertyFormulaPreorder.refl φ)

/-- A formula is below its self-disjunction in the generated formula preorder. -/
theorem PropertyFormulaPreorder.le_disj_self {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var φ (PropertyExpr.disj φ φ) := by
  exact PropertyFormulaPreorder.le_disj_left φ φ

/-- Derived conjunction associativity transport for displayed derivations. -/
theorem DomainLogicDerivation.conj_assoc {Var : Type u}
    {s : PropertySequent Var} {φ ψ χ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj (PropertyExpr.conj φ ψ) χ))) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj φ (PropertyExpr.conj ψ χ))) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.conj_assoc φ ψ χ))

/-- Derived reverse conjunction associativity transport for displayed
derivations. -/
theorem DomainLogicDerivation.conj_assoc_symm {Var : Type u}
    {s : PropertySequent Var} {φ ψ χ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj φ (PropertyExpr.conj ψ χ)))) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj (PropertyExpr.conj φ ψ) χ)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.conj_assoc_symm φ ψ χ))

/-- Derived disjunction associativity transport for displayed derivations. -/
theorem DomainLogicDerivation.disj_assoc {Var : Type u}
    {s : PropertySequent Var} {φ ψ χ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj (PropertyExpr.disj φ ψ) χ))) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj φ (PropertyExpr.disj ψ χ))) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.disj_assoc φ ψ χ))

/-- Derived reverse disjunction associativity transport for displayed
derivations. -/
theorem DomainLogicDerivation.disj_assoc_symm {Var : Type u}
    {s : PropertySequent Var} {φ ψ χ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj φ (PropertyExpr.disj ψ χ)))) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj (PropertyExpr.disj φ ψ) χ)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.disj_assoc_symm φ ψ χ))

/-- Derived conjunction idempotence transport for displayed derivations. -/
theorem DomainLogicDerivation.conj_idem {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj φ φ))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.conj_idem φ))

/-- A derivation can be duplicated into a self-conjunction. -/
theorem DomainLogicDerivation.conj_intro_self {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.conj φ φ)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.le_conj_self φ))

/-- Derived disjunction idempotence transport for displayed derivations. -/
theorem DomainLogicDerivation.disj_idem {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj φ φ))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.disj_idem φ))

/-- A derivation can be injected into a self-disjunction. -/
theorem DomainLogicDerivation.disj_intro_self {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s (PropertyExpr.disj φ φ)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.le_disj_self φ))

/-- Conjunction absorbs a disjunction containing the left conjunct. -/
theorem PropertyFormulaPreorder.conj_absorb {Var : Type u} {σ : TypeExpr Var}
    (φ ψ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.conj φ (PropertyExpr.disj φ ψ)) φ := by
  exact PropertyFormulaPreorder.conj_left φ (PropertyExpr.disj φ ψ)

/-- A formula is below its conjunction with a disjunction containing itself. -/
theorem PropertyFormulaPreorder.le_conj_absorb {Var : Type u}
    {σ : TypeExpr Var} (φ ψ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var φ
      (PropertyExpr.conj φ (PropertyExpr.disj φ ψ)) := by
  exact
    PropertyFormulaPreorder.conj_intro
      (PropertyFormulaPreorder.refl φ)
      (PropertyFormulaPreorder.le_disj_left φ ψ)

/-- Disjunction absorbs a conjunction containing the left disjunct. -/
theorem PropertyFormulaPreorder.disj_absorb {Var : Type u} {σ : TypeExpr Var}
    (φ ψ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.disj φ (PropertyExpr.conj φ ψ)) φ := by
  exact
    PropertyFormulaPreorder.disj_elim
      (PropertyFormulaPreorder.refl φ)
      (PropertyFormulaPreorder.conj_left φ ψ)

/-- A formula is below its disjunction with a conjunction containing itself. -/
theorem PropertyFormulaPreorder.le_disj_absorb {Var : Type u}
    {σ : TypeExpr Var} (φ ψ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var φ
      (PropertyExpr.disj φ (PropertyExpr.conj φ ψ)) := by
  exact PropertyFormulaPreorder.le_disj_left φ (PropertyExpr.conj φ ψ)

/-- Derived conjunction absorption transport for displayed derivations. -/
theorem DomainLogicDerivation.conj_absorb {Var : Type u}
    {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj φ (PropertyExpr.disj φ ψ)))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.conj_absorb φ ψ))

/-- A displayed derivation can be expanded by conjunction absorption. -/
theorem DomainLogicDerivation.conj_intro_absorb {Var : Type u}
    {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj φ (PropertyExpr.disj φ ψ))) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.le_conj_absorb φ ψ))

/-- Derived disjunction absorption transport for displayed derivations. -/
theorem DomainLogicDerivation.disj_absorb {Var : Type u}
    {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj φ (PropertyExpr.conj φ ψ)))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.disj_absorb φ ψ))

/-- A displayed derivation can be expanded by disjunction absorption. -/
theorem DomainLogicDerivation.disj_intro_absorb {Var : Type u}
    {s : PropertySequent Var} {φ ψ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj φ (PropertyExpr.conj φ ψ))) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.le_disj_absorb φ ψ))

/-- Truth is a right unit for conjunction in the generated formula preorder. -/
theorem PropertyFormulaPreorder.conj_truth {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.conj φ (PropertyExpr.truth : PropertyExpr Var σ)) φ := by
  exact
    PropertyFormulaPreorder.conj_left φ
      (PropertyExpr.truth : PropertyExpr Var σ)

/-- A formula is below its conjunction with truth on the right. -/
theorem PropertyFormulaPreorder.le_conj_truth {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var φ
      (PropertyExpr.conj φ (PropertyExpr.truth : PropertyExpr Var σ)) := by
  exact
    PropertyFormulaPreorder.conj_intro
      (PropertyFormulaPreorder.refl φ)
      (PropertyFormulaPreorder.le_true φ)

/-- Truth is a left unit for conjunction in the generated formula preorder. -/
theorem PropertyFormulaPreorder.truth_conj {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.conj (PropertyExpr.truth : PropertyExpr Var σ) φ) φ := by
  exact
    PropertyFormulaPreorder.conj_right
      (PropertyExpr.truth : PropertyExpr Var σ) φ

/-- A formula is below its conjunction with truth on the left. -/
theorem PropertyFormulaPreorder.le_truth_conj {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var φ
      (PropertyExpr.conj (PropertyExpr.truth : PropertyExpr Var σ) φ) := by
  exact
    PropertyFormulaPreorder.conj_intro
      (PropertyFormulaPreorder.le_true φ)
      (PropertyFormulaPreorder.refl φ)

/-- Falsity is a right unit for disjunction in the generated formula preorder. -/
theorem PropertyFormulaPreorder.disj_falsity {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.disj φ (PropertyExpr.falsity : PropertyExpr Var σ)) φ := by
  exact
    PropertyFormulaPreorder.disj_elim
      (PropertyFormulaPreorder.refl φ)
      (PropertyFormulaPreorder.false_le φ)

/-- A formula is below its disjunction with falsity on the right. -/
theorem PropertyFormulaPreorder.le_disj_falsity {Var : Type u}
    {σ : TypeExpr Var} (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var φ
      (PropertyExpr.disj φ (PropertyExpr.falsity : PropertyExpr Var σ)) := by
  exact
    PropertyFormulaPreorder.le_disj_left φ
      (PropertyExpr.falsity : PropertyExpr Var σ)

/-- Falsity is a left unit for disjunction in the generated formula preorder. -/
theorem PropertyFormulaPreorder.falsity_disj {Var : Type u} {σ : TypeExpr Var}
    (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var
      (PropertyExpr.disj (PropertyExpr.falsity : PropertyExpr Var σ) φ) φ := by
  exact
    PropertyFormulaPreorder.disj_elim
      (PropertyFormulaPreorder.false_le φ)
      (PropertyFormulaPreorder.refl φ)

/-- A formula is below its disjunction with falsity on the left. -/
theorem PropertyFormulaPreorder.le_falsity_disj {Var : Type u}
    {σ : TypeExpr Var} (φ : PropertyExpr Var σ) :
    PropertyFormulaPreorder Var φ
      (PropertyExpr.disj (PropertyExpr.falsity : PropertyExpr Var σ) φ) := by
  exact
    PropertyFormulaPreorder.le_disj_right
      (PropertyExpr.falsity : PropertyExpr Var σ) φ

/-- Derived right-truth conjunction transport for displayed derivations. -/
theorem DomainLogicDerivation.conj_truth {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj φ
          (PropertyExpr.truth : PropertyExpr Var s.σ)))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.conj_truth φ))

/-- A displayed derivation can be expanded by conjoining truth on the right. -/
theorem DomainLogicDerivation.conj_intro_truth {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj φ
          (PropertyExpr.truth : PropertyExpr Var s.σ))) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.le_conj_truth φ))

/-- Derived left-truth conjunction transport for displayed derivations. -/
theorem DomainLogicDerivation.truth_conj {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj
          (PropertyExpr.truth : PropertyExpr Var s.σ) φ))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.truth_conj φ))

/-- A displayed derivation can be expanded by conjoining truth on the left. -/
theorem DomainLogicDerivation.truth_conj_intro {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.conj
          (PropertyExpr.truth : PropertyExpr Var s.σ) φ)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.le_truth_conj φ))

/-- Derived right-falsity disjunction transport for displayed derivations. -/
theorem DomainLogicDerivation.disj_falsity {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj φ
          (PropertyExpr.falsity : PropertyExpr Var s.σ)))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.disj_falsity φ))

/-- A displayed derivation can be expanded by disjoining falsity on the right. -/
theorem DomainLogicDerivation.disj_intro_falsity {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj φ
          (PropertyExpr.falsity : PropertyExpr Var s.σ))) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.le_disj_falsity φ))

/-- Derived left-falsity disjunction transport for displayed derivations. -/
theorem DomainLogicDerivation.falsity_disj {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj
          (PropertyExpr.falsity : PropertyExpr Var s.σ) φ))) :
    DomainLogicDerivation Var (PropertySequent.withProperty s φ) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.falsity_disj φ))

/-- A displayed derivation can be expanded by disjoining falsity on the left. -/
theorem DomainLogicDerivation.falsity_disj_intro {Var : Type u}
    {s : PropertySequent Var} {φ : PropertyExpr Var s.σ}
    (h : DomainLogicDerivation Var (PropertySequent.withProperty s φ)) :
    DomainLogicDerivation Var
      (PropertySequent.withProperty s
        (PropertyExpr.disj
          (PropertyExpr.falsity : PropertyExpr Var s.σ) φ)) := by
  simpa [PropertySequent.withProperty] using
    (DomainLogicDerivation.preorder h
      (PropertyFormulaPreorder.le_falsity_disj φ))

/-- Coverage of the sequent-calculus rules displayed before Theorem 7.3.18. -/
structure DomainLogicRuleCoverage (Var : Type u) where
  FormulaFilterSideCondition : {σ : TypeExpr Var} → Set (PropertyExpr Var σ) → Prop
  formula_filter_side_condition_matches_syntax :
    ∀ {σ : TypeExpr Var} (F : Set (PropertyExpr Var σ)),
      FormulaFilterSideCondition F ↔ PropertyFormulaPrimeFilter Var F
  preorder_weakening_rules : Prop
  PrimeContextSideCondition : List (PropertyAssumption Var) → Prop
  prime_context_side_condition_matches_syntax :
    ∀ Γ : List (PropertyAssumption Var),
      PrimeContextSideCondition Γ ↔ PropertyContextPrime Γ
  structural_weakening_rule : Prop
  variable_rule : Prop
  function_rules : Prop
  product_rules : Prop
  sum_and_case_rules : Prop
  lifting_rules : Prop
  plotkin_singleton_and_bind_rules : Prop
  plotkin_union_and_tensor_rules : Prop
  recursive_fold_unfold_rules : Prop
  fixpoint_rule : Prop
  positive_inductive_presentation : Prop

/-- A sound-and-complete sequent calculus package for the domain logic. -/
structure DomainLogicSoundComplete (Var : Type u) where
  Environment : Type u
  SatisfiesAssumption : Environment → PropertyAssumption Var → Prop
  TermSatisfiesProperty : Environment → PropertySequent Var → Prop
  DisplayedRuleDerivation : PropertySequent Var → Prop
  displayed_rule_derivation_matches_syntax :
    ∀ s : PropertySequent Var, DisplayedRuleDerivation s ↔ DomainLogicDerivation Var s
  Derivable : PropertySequent Var → Prop
  Valid : PropertySequent Var → Prop
  rule_coverage : DomainLogicRuleCoverage Var
  denotational_semantics_respects_types : Prop
  context_agreement_matches_pdf : Prop
  derivability_positive_inductive : Prop
  validity_matches_denotational_semantics :
    ∀ s : PropertySequent Var,
      Valid s ↔
        ∀ ρ : Environment,
          (∀ a : PropertyAssumption Var, a ∈ s.context → SatisfiesAssumption ρ a) →
            TermSatisfiesProperty ρ s
  sound_complete : ∀ s : PropertySequent Var, Derivable s ↔ Valid s

private theorem punit_scottOpen (U : Set PUnit) :
    @Chapter2.ScottOpen PUnit inferInstance U := by
  constructor
  · intro x y hy _hxy
    cases x
    cases y
    exact hy
  · intro A s hA hsub _hs
    cases s
    rcases hA.1 with ⟨a, ha⟩
    cases a
    exact hsub ha

private theorem punit_scottContinuous_const {D : Type u} [Preorder D] :
    @Chapter3.ScottContinuous D PUnit inferInstance inferInstance (fun _ => PUnit.unit) := by
  constructor
  · intro x y _hxy
    exact le_rfl
  · intro A s _hA _hs
    constructor
    · intro y hy
      rcases hy with ⟨a, _ha, rfl⟩
      exact le_rfl
    · intro y _hy
      cases y
      exact le_rfl

private def punitOrderedDomain : Chapter4.OrderedDomain.{u} where
  carrier := PUnit
  preorder := inferInstance

private def punitFiniteProjection : Chapter4.FiniteProjection punitOrderedDomain.{u} where
  toFun := fun x => x
  continuous := Chapter3.scottContinuous_id
  idem := by
    intro x
    rfl
  below := by
    intro x
    exact le_rfl
  finite_range := by
    exact (Set.finite_singleton PUnit.unit).subset (by
      intro x _hx
      cases x
      simp)

private def punitBifiniteDomain : Chapter4.BifiniteDomain.{u} where
  object := punitOrderedDomain
  projection := fun _ => punitFiniteProjection
  increasing := by
    intro n x
    exact le_rfl
  approximates := by
    intro x
    constructor
    · intro y _hy
      cases x
      cases y
      exact le_rfl
    · intro y _hy
      cases x
      cases y
      exact le_rfl

private theorem punit_univ_joinPrime :
    IsJoinPrimeRel
      (fun x y : Set PUnit => x ⊆ y) (fun x y => x ∪ y) ∅ Set.univ := by
  constructor
  · intro hzero
    exact hzero.1 (show PUnit.unit ∈ (Set.univ : Set PUnit) from trivial)
  · intro b c habc
    have hbc : PUnit.unit ∈ b ∪ c := habc trivial
    rcases hbc with hb | hc
    · left
      intro x _hx
      cases x
      exact hb
    · right
      intro x _hx
      cases x
      exact hc

private theorem punit_open_joinPrime_iff (a : Set PUnit) :
    a = Set.univ ↔
      IsJoinPrimeRel
        (fun x y : Set PUnit => x ⊆ y) (fun x y => x ∪ y) ∅ a := by
  constructor
  · intro ha
    simpa [ha] using punit_univ_joinPrime
  · intro hprime
    by_cases hunit : PUnit.unit ∈ a
    · ext x
      cases x
      constructor
      · intro _hx
        trivial
      · intro _hx
        exact hunit
    · have haEmpty : a = ∅ := by
        ext x
        cases x
        constructor
        · intro hx
          exact False.elim (hunit hx)
        · intro hx
          cases hx
      exact False.elim (hprime.1 ⟨by simp [haEmpty], by simp [haEmpty]⟩)

private def punitOpenPrelocale : DomainPrelocale.{u} where
  carrier := Set PUnit
  le := fun U V => U ⊆ V
  le_refl := by
    intro U x hx
    exact hx
  le_trans := by
    intro U V W hUV hVW x hx
    exact hVW (hUV hx)
  sup := fun U V => U ∪ V
  inf := fun U V => U ∩ V
  zero := ∅
  one := Set.univ
  C := fun U => U = Set.univ
  sup_is_sup := by
    intro a b c
    exact Set.union_subset_iff
  inf_is_inf := by
    intro a b c
    exact Set.subset_inter_iff
  zero_le := by
    intro a x hx
    cases hx
  le_one := by
    intro a x _hx
    trivial
  C_iff_join_prime := by
    intro a
    exact punit_open_joinPrime_iff a
  finite_prime_generation := by
    intro a
    by_cases hunit : PUnit.unit ∈ a
    · have ha : a = Set.univ := by
        ext x
        cases x
        constructor
        · intro _hx
          trivial
        · intro _hx
          exact hunit
      refine ⟨[Set.univ], ?_, ?_⟩
      · intro x hx
        simpa using hx
      · constructor <;> intro x hx
        · simpa [ListJoin, ha] using hx
        · simpa [ListJoin, ha] using hx
    · have ha : a = ∅ := by
        ext x
        cases x
        constructor
        · intro hx
          exact False.elim (hunit hx)
        · intro hx
          cases hx
      refine ⟨[], ?_, ?_⟩
      · intro x hx
        cases hx
      · constructor <;> intro x hx
        · simpa [ListJoin, ha] using hx
        · simpa [ListJoin, ha] using hx
  finite_mub_closure := by
    intro U _hUfin hUC
    let onlyTop : Set (Set PUnit) := {Set.univ}
    refine ⟨onlyTop, ?_, ?_, ?_, ?_⟩
    · simp [onlyTop]
    · intro S hS
      simpa [onlyTop, hUC S hS]
    · intro S hS
      simpa [onlyTop] using hS
    · intro W hWV
      refine ⟨onlyTop, (by intro z hz; simpa [onlyTop] using hz), ?_⟩
      refine ⟨Set.univ, Set.univ, ?_, ?_, ?_⟩
      · constructor
        · intro w hw
          have hwEq : w = Set.univ := by
            simpa [onlyTop] using hWV hw
          intro x _hx
          simpa [hwEq]
        · intro y _hy x _hx
          trivial
      · constructor
        · intro z hz
          have hzEq : z = Set.univ := by
            simpa [onlyTop] using hz
          intro x hx
          simpa [hzEq] using hx
        · intro y hy
          have huniv_mem : (Set.univ : Set PUnit) ∈ onlyTop := by
            simp [onlyTop]
          exact hy Set.univ huniv_mem
      · constructor <;> intro x hx <;> exact hx
  top_prime := rfl

private theorem punit_scottCompact (K : Set PUnit) :
    ScottCompactSet punitOrderedDomain.{u} K := by
  intro cover _hcover hsub
  by_cases hK : ∃ x : PUnit, x ∈ K
  · rcases hK with ⟨x, hx⟩
    cases x
    have hUnion : PUnit.unit ∈ ⋃₀ cover := hsub hx
    rcases hUnion with ⟨U, hUcover, hUunit⟩
    refine ⟨{U}, Set.finite_singleton U, ?_, ?_⟩
    · intro V hV
      simpa using hV ▸ hUcover
    · intro y _hy
      cases y
      exact ⟨U, by simp, hUunit⟩
  · refine ⟨∅, Set.finite_empty, ?_, ?_⟩
    · intro U hU
      cases hU
    · intro x hx
      exact False.elim (hK ⟨x, hx⟩)

private theorem punit_compact_unit :
    @Chapter2.Compact PUnit inferInstance PUnit.unit := by
  intro A _s hA _hs _hle
  rcases hA.1 with ⟨a, haA⟩
  refine ⟨a, haA, ?_⟩
  cases a
  exact le_rfl

private def punitLocalicDescription :
    LocalicDescription punitOpenPrelocale.{u} punitBifiniteDomain.{u} where
  interpret := fun U =>
    { carrier := U
      scott_open := punit_scottOpen U
      compact := punit_scottCompact U }
  surjective := by
    intro O
    exact ⟨O.carrier, rfl⟩
  order_preserving := by
    intro a b hab
    exact hab
  order_reflecting := by
    intro a b hab
    exact hab
  sup_preserving := by
    intro a b
    rfl
  inf_preserving := by
    intro a b
    rfl
  zero_preserving := rfl
  one_preserving := rfl
  C_to_principal := by
    intro a ha
    refine ⟨PUnit.unit, punit_compact_unit, ?_⟩
    ext x
    cases x
    constructor
    · intro _hx
      trivial
    · intro _hx
      rw [ha]
      trivial
  principal_surjective := by
    intro O hO
    rcases hO with ⟨c, _hc, hcarrier⟩
    refine ⟨Set.univ, rfl, ?_⟩
    have hOuniv : O.carrier = Set.univ := by
      rw [hcarrier]
      ext x
      cases x
      cases c
      simp
    rw [hOuniv]
    rfl

private theorem punit_set_empty_or_univ (U : Set PUnit) :
    U = ∅ ∨ U = Set.univ := by
  by_cases hunit : PUnit.unit ∈ U
  · right
    ext x
    cases x
    constructor
    · intro _hx
      trivial
    · intro _hx
      exact hunit
  · left
    ext x
    cases x
    constructor
    · intro hx
      exact False.elim (hunit hx)
    · intro hx
      cases hx

private theorem punit_set_univ_of_unit_mem {U : Set PUnit} (hunit : PUnit.unit ∈ U) :
    U = Set.univ := by
  ext x
  cases x
  constructor
  · intro _hx
    trivial
  · intro _hx
    exact hunit

/-- The unique proper prime filter of the unit prelocale. -/
private def punitTopSpec : Spec punitOpenPrelocale.{u} :=
  ⟨{U : Set PUnit | U = Set.univ}, by
    refine
      { one_mem := ?_
        zero_not_mem := ?_
        upward_closed := ?_
        inf_closed := ?_
        sup_prime := ?_ }
    · rfl
    · intro hEmpty
      change (∅ : Set PUnit) = Set.univ at hEmpty
      have hUnit : PUnit.unit ∈ (∅ : Set PUnit) := by
        rw [hEmpty]
        trivial
      exact hUnit
    · intro U V hU hUV
      change (U : Set PUnit) = Set.univ at hU
      change (V : Set PUnit) = Set.univ
      have hUVset : (show Set PUnit from U) ⊆ (show Set PUnit from V) := by
        simpa [punitOpenPrelocale] using hUV
      have hUunit : PUnit.unit ∈ (show Set PUnit from U) := by
        rw [hU]
        trivial
      have hVunit : PUnit.unit ∈ (show Set PUnit from V) := by
        exact hUVset hUunit
      exact punit_set_univ_of_unit_mem hVunit
    · intro U V hU hV
      change (U : Set PUnit) = Set.univ at hU
      change (V : Set PUnit) = Set.univ at hV
      change (show Set PUnit from punitOpenPrelocale.inf U V) = Set.univ
      simpa [punitOpenPrelocale, hU, hV]
    · intro U V hUV
      change (show Set PUnit from punitOpenPrelocale.sup U V) = Set.univ at hUV
      have hUnit :
          PUnit.unit ∈ (show Set PUnit from punitOpenPrelocale.sup U V) := by
        rw [hUV]
        trivial
      have hUnion : PUnit.unit ∈ (show Set PUnit from U) ∪ (show Set PUnit from V) := by
        simpa [punitOpenPrelocale] using hUnit
      rcases hUnion with hU | hV
      · left
        change (U : Set PUnit) = Set.univ
        exact punit_set_univ_of_unit_mem hU
      · right
        change (V : Set PUnit) = Set.univ
        exact punit_set_univ_of_unit_mem hV⟩

private theorem punitSpec_unique (F : Spec punitOpenPrelocale.{u}) :
    F = punitTopSpec := by
  apply Subtype.ext
  ext U
  constructor
  · intro hU
    rcases punit_set_empty_or_univ U with hEmpty | hUniv
    · exact False.elim (F.2.zero_not_mem (by simpa [punitOpenPrelocale, hEmpty] using hU))
    · change (U : Set PUnit) = Set.univ
      exact hUniv
  · intro hU
    have hUniv : U = Set.univ := by
      change (U : Set PUnit) = Set.univ at hU
      exact hU
    simpa [punitOpenPrelocale, hUniv] using F.2.one_mem

/-- The corrected proper-filter spectrum of the unit prelocale is isomorphic to
the unit bifinite domain. -/
private def punitSpecDomainIso :
    SpecDomainIso punitOpenPrelocale.{u} punitBifiniteDomain.{u} where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => punitTopSpec
  left_inv := by
    intro F
    exact (punitSpec_unique F).symm
  right_inv := by
    intro x
    cases x
    rfl
  order_compatible := by
    intro F G
    constructor
    · intro _h
      exact le_rfl
    · intro _h U hU
      simpa [punitSpec_unique F, punitSpec_unique G] using hU

/-- Denotation of the property language for the closed unit type as subsets of
the one-point space. -/
private def punitPropertyDenoteSet :
    PropertyExpr Empty (.one : ClosedTypeExpr) → Set PUnit
  | PropertyExpr.truth => (Set.univ : Set PUnit)
  | PropertyExpr.falsity => (∅ : Set PUnit)
  | PropertyExpr.conj φ ψ => punitPropertyDenoteSet φ ∩ punitPropertyDenoteSet ψ
  | PropertyExpr.disj φ ψ => punitPropertyDenoteSet φ ∪ punitPropertyDenoteSet ψ

/-- Boolean evaluation of closed-unit property expressions. -/
private def punitPropertyTruthValue :
    PropertyExpr Empty (.one : ClosedTypeExpr) → Bool
  | PropertyExpr.truth => true
  | PropertyExpr.falsity => false
  | PropertyExpr.conj φ ψ => punitPropertyTruthValue φ && punitPropertyTruthValue ψ
  | PropertyExpr.disj φ ψ => punitPropertyTruthValue φ || punitPropertyTruthValue ψ

/-- On the one-point interpretation, a unit formula denotes exactly its Boolean
truth value. -/
private theorem punitPropertyDenoteSet_unit_iff :
    ∀ φ : PropertyExpr Empty (.one : ClosedTypeExpr),
      PUnit.unit ∈ punitPropertyDenoteSet φ ↔ punitPropertyTruthValue φ = true
  | PropertyExpr.truth => by
      simp [punitPropertyDenoteSet, punitPropertyTruthValue]
  | PropertyExpr.falsity => by
      simp [punitPropertyDenoteSet, punitPropertyTruthValue]
  | PropertyExpr.conj φ ψ => by
      simp [punitPropertyDenoteSet, punitPropertyTruthValue,
        punitPropertyDenoteSet_unit_iff φ, punitPropertyDenoteSet_unit_iff ψ]
  | PropertyExpr.disj φ ψ => by
      simp [punitPropertyDenoteSet, punitPropertyTruthValue,
        punitPropertyDenoteSet_unit_iff φ, punitPropertyDenoteSet_unit_iff ψ]

/-- Inclusion between closed-unit property denotations is Boolean implication. -/
private theorem punitPropertyDenoteSet_subset_iff
    (φ ψ : PropertyExpr Empty (.one : ClosedTypeExpr)) :
    punitPropertyDenoteSet φ ⊆ punitPropertyDenoteSet ψ ↔
      (punitPropertyTruthValue φ = true → punitPropertyTruthValue ψ = true) := by
  constructor
  · intro h hφ
    exact (punitPropertyDenoteSet_unit_iff ψ).1
      (h ((punitPropertyDenoteSet_unit_iff φ).2 hφ))
  · intro h x hx
    cases x
    exact (punitPropertyDenoteSet_unit_iff ψ).2
      (h ((punitPropertyDenoteSet_unit_iff φ).1 hx))

/-- The base `L(1)` preorder used by the decidability proof is decidable in the
concrete one-point interpretation. -/
private def punitPropertyLanguagePreorder_decidable
    (φ ψ : PropertyExpr Empty (.one : ClosedTypeExpr)) :
    Decidable (punitOpenPrelocale.le (punitPropertyDenoteSet φ) (punitPropertyDenoteSet ψ)) := by
  dsimp [punitOpenPrelocale]
  by_cases h :
      punitPropertyTruthValue φ = true → punitPropertyTruthValue ψ = true
  · exact isTrue ((punitPropertyDenoteSet_subset_iff φ ψ).2 h)
  · exact isFalse (fun hle => h ((punitPropertyDenoteSet_subset_iff φ ψ).1 hle))

/-- The syntactic prelocale for the closed unit type, interpreted in the
one-point prelocale. -/
private def punitPropertyLanguagePrelocale :
    PropertyLanguagePrelocale.{u} (.one : ClosedTypeExpr) where
  prelocale := punitOpenPrelocale
  denote := punitPropertyDenoteSet
  truth_is_one := by
    constructor <;> intro x hx <;>
      simpa [punitPropertyDenoteSet, punitOpenPrelocale] using hx
  falsity_is_zero := by
    constructor <;> intro x hx <;>
      simpa [punitPropertyDenoteSet, punitOpenPrelocale] using hx
  conj_is_inf := by
    intro φ ψ
    constructor <;> intro x hx <;>
      simpa [punitPropertyDenoteSet, punitOpenPrelocale] using hx
  disj_is_sup := by
    intro φ ψ
    constructor <;> intro x hx <;>
      simpa [punitPropertyDenoteSet, punitOpenPrelocale] using hx
  generated_by_properties := by
    intro U
    rcases punit_set_empty_or_univ U with hEmpty | hUniv
    · refine ⟨PropertyExpr.falsity, ?_⟩
      constructor <;> intro x hx <;>
        simpa [punitPropertyDenoteSet, punitOpenPrelocale, hEmpty] using hx
    · refine ⟨PropertyExpr.truth, ?_⟩
      constructor <;> intro x hx <;>
        simpa [punitPropertyDenoteSet, punitOpenPrelocale, hUniv] using hx
  preorder_lattice_rules := by
    refine
      { refl := ?_
        trans := ?_
        le_true := ?_
        conj_intro := ?_
        conj_left := ?_
        conj_right := ?_
        false_le := ?_
        disj_elim := ?_
        le_disj_left := ?_
        le_disj_right := ?_
        distributivity := ?_ }
    · intro φ x hx
      exact hx
    · intro φ ψ χ hφψ hψχ x hx
      exact hψχ (hφψ hx)
    · intro φ x _hx
      simpa [punitPropertyDenoteSet]
    · intro φ ψ₁ ψ₂ hφψ₁ hφψ₂ x hx
      simpa [punitPropertyDenoteSet] using ⟨hφψ₁ hx, hφψ₂ hx⟩
    · intro φ ψ x hx
      have hx' : x ∈ punitPropertyDenoteSet φ ∩ punitPropertyDenoteSet ψ := by
        simpa [punitPropertyDenoteSet] using hx
      exact hx'.1
    · intro φ ψ x hx
      have hx' : x ∈ punitPropertyDenoteSet φ ∩ punitPropertyDenoteSet ψ := by
        simpa [punitPropertyDenoteSet] using hx
      exact hx'.2
    · intro φ x hx
      simpa [punitPropertyDenoteSet] using hx
    · intro φ₁ φ₂ ψ hφ₁ψ hφ₂ψ x hx
      rcases (by simpa [punitPropertyDenoteSet] using hx :
          x ∈ punitPropertyDenoteSet φ₁ ∪ punitPropertyDenoteSet φ₂) with hx | hx
      · exact hφ₁ψ hx
      · exact hφ₂ψ hx
    · intro φ ψ x hx
      simpa [punitPropertyDenoteSet] using
        (Or.inl hx :
          x ∈ punitPropertyDenoteSet φ ∪ punitPropertyDenoteSet ψ)
    · intro φ ψ x hx
      simpa [punitPropertyDenoteSet] using
        (Or.inr hx :
          x ∈ punitPropertyDenoteSet φ ∪ punitPropertyDenoteSet ψ)
    · intro φ ψ χ x hx
      rcases (by simpa [punitPropertyDenoteSet] using hx :
          x ∈ punitPropertyDenoteSet φ ∩
            (punitPropertyDenoteSet ψ ∪ punitPropertyDenoteSet χ)) with
        ⟨hxφ, hxψ | hxχ⟩
      · have hxφψ : x ∈ punitPropertyDenoteSet (PropertyExpr.conj φ ψ) := by
          simpa [punitPropertyDenoteSet] using ⟨hxφ, hxψ⟩
        simpa [punitPropertyDenoteSet] using
          (Or.inl hxφψ :
            x ∈
              punitPropertyDenoteSet (PropertyExpr.conj φ ψ) ∪
                punitPropertyDenoteSet (PropertyExpr.conj φ χ))
      · have hxφχ : x ∈ punitPropertyDenoteSet (PropertyExpr.conj φ χ) := by
          simpa [punitPropertyDenoteSet] using ⟨hxφ, hxχ⟩
        simpa [punitPropertyDenoteSet] using
          (Or.inr hxφχ :
            x ∈
              punitPropertyDenoteSet (PropertyExpr.conj φ ψ) ∪
                punitPropertyDenoteSet (PropertyExpr.conj φ χ))
  type_specific_preorder_rules := True
  compact_predicate_generated_by_rules := True
  termination_predicate_generated_by_rules := True

/-- A compatibility package for the two interpretations of type expressions.
It records the semantic clauses displayed in the PDF, plus localic-description
compatibility for the constructors whose concrete domain objects are represented
elsewhere in the formalization. -/
structure TypeInterpretationAgreement (Var : Type u) where
  localicEnv : Var → DomainPrelocale.{u}
  domainEnv : Var → Chapter4.BifiniteDomain.{u}
  env_describes : ∀ X : Var, Nonempty (LocalicDescription (localicEnv X) (domainEnv X))
  localicInterpretation : TypeExpr Var → DomainPrelocale.{u}
  domainInterpretation : TypeExpr Var → Chapter4.BifiniteDomain.{u}
  one_localic_clause :
    localicInterpretation .one = punitOpenPrelocale.{u}
  one_domain_clause :
    domainInterpretation .one = punitBifiniteDomain.{u}
  one_describes :
    Nonempty (LocalicDescription (localicInterpretation .one) (domainInterpretation .one))
  var_localic_clause :
    ∀ X : Var, localicInterpretation (.var X) = localicEnv X
  var_domain_clause :
    ∀ X : Var, domainInterpretation (.var X) = domainEnv X
  function_space_localic_clause :
    ∀ σ τ : TypeExpr Var,
      ∃ F : FunctionSpacePrelocaleDescription
          (localicInterpretation σ) (localicInterpretation τ),
        F.prelocale = localicInterpretation (.arr σ τ)
  function_space_domain_clause :
    ∀ σ τ : TypeExpr Var,
      (domainInterpretation (.arr σ τ)).object =
        Chapter4.OrderedDomain.functionSpace
          (domainInterpretation σ).object (domainInterpretation τ).object
  product_localic_clause :
    ∀ σ τ : TypeExpr Var,
      Nonempty (LocalicDescription
        (localicInterpretation (.prod σ τ)) (domainInterpretation (.prod σ τ)))
  product_domain_clause :
    ∀ σ τ : TypeExpr Var,
      (domainInterpretation (.prod σ τ)).object =
        Chapter4.OrderedDomain.prod
          (domainInterpretation σ).object (domainInterpretation τ).object
  sum_localic_clause :
    ∀ σ τ : TypeExpr Var,
      Nonempty (LocalicDescription
        (localicInterpretation (.sum σ τ)) (domainInterpretation (.sum σ τ)))
  lift_localic_clause :
    ∀ σ : TypeExpr Var,
      Nonempty (LocalicDescription
        (localicInterpretation (.lift σ)) (domainInterpretation (.lift σ)))
  plotkin_localic_clause :
    ∀ σ : TypeExpr Var,
      ∃ P : PlotkinPowerlocaleDescription (localicInterpretation σ),
        P.prelocale = localicInterpretation (.plotkin σ)
  plotkin_domain_clause :
    ∀ σ : TypeExpr Var,
      ∃ R : PlotkinLensRepresentation (domainInterpretation σ).object,
        R.powerdomain.carrier = (domainInterpretation (.plotkin σ)).object
  recursive_localic_clause :
    ∀ X : Var, ∀ σ : TypeExpr Var,
      ∃ C : PrelocaleChain.{u}, ∃ B : PrelocaleChainBilimitDescription C,
        B.union = localicInterpretation (.recTy X σ) ∧
          B.bilimit_domain = domainInterpretation (.recTy X σ)
  interpretations_describe :
    ∀ σ : TypeExpr Var,
      Nonempty (LocalicDescription (localicInterpretation σ) (domainInterpretation σ))

/-- Closed-type specialization of the interpretation clauses, avoiding a universe
collapse through `Empty` environments while still tying closed syntactic
prelocales to the corresponding bifinite-domain interpretation. -/
structure ClosedTypeInterpretationAgreement where
  localicInterpretation : ClosedTypeExpr → DomainPrelocale.{u}
  domainInterpretation : ClosedTypeExpr → Chapter4.BifiniteDomain.{u}
  one_localic_clause :
    localicInterpretation .one = punitOpenPrelocale.{u}
  one_domain_clause :
    domainInterpretation .one = punitBifiniteDomain.{u}
  function_space_localic_clause :
    ∀ σ τ : ClosedTypeExpr,
      ∃ F : FunctionSpacePrelocaleDescription
          (localicInterpretation σ) (localicInterpretation τ),
        F.prelocale = localicInterpretation (.arr σ τ)
  function_space_domain_clause :
    ∀ σ τ : ClosedTypeExpr,
      (domainInterpretation (.arr σ τ)).object =
        Chapter4.OrderedDomain.functionSpace
          (domainInterpretation σ).object (domainInterpretation τ).object
  product_localic_clause :
    ∀ σ τ : ClosedTypeExpr,
      Nonempty (LocalicDescription
        (localicInterpretation (.prod σ τ)) (domainInterpretation (.prod σ τ)))
  product_domain_clause :
    ∀ σ τ : ClosedTypeExpr,
      (domainInterpretation (.prod σ τ)).object =
        Chapter4.OrderedDomain.prod
          (domainInterpretation σ).object (domainInterpretation τ).object
  sum_localic_clause :
    ∀ σ τ : ClosedTypeExpr,
      Nonempty (LocalicDescription
        (localicInterpretation (.sum σ τ)) (domainInterpretation (.sum σ τ)))
  lift_localic_clause :
    ∀ σ : ClosedTypeExpr,
      Nonempty (LocalicDescription
        (localicInterpretation (.lift σ)) (domainInterpretation (.lift σ)))
  plotkin_localic_clause :
    ∀ σ : ClosedTypeExpr,
      ∃ P : PlotkinPowerlocaleDescription (localicInterpretation σ),
        P.prelocale = localicInterpretation (.plotkin σ)
  plotkin_domain_clause :
    ∀ σ : ClosedTypeExpr,
      ∃ R : PlotkinLensRepresentation (domainInterpretation σ).object,
        R.powerdomain.carrier = (domainInterpretation (.plotkin σ)).object
  interpretations_describe :
    ∀ σ : ClosedTypeExpr,
      Nonempty (LocalicDescription (localicInterpretation σ) (domainInterpretation σ))

/-- The localic spectrum description of the current closed-fragment expression.
The returned
prelocale is explicitly tied to the syntactic property language `L(σ)` and to
closed localic/domain interpretations of the same expression. -/
structure ClosedTypeSpectrumDescription (σ : ClosedTypeExpr) where
  prelocale : DomainPrelocale.{u}
  domain : Chapter4.BifiniteDomain.{u}
  property_language : PropertyLanguagePrelocale.{u} σ
  prelocale_eq_property_language : prelocale = property_language.prelocale
  describes : Nonempty (LocalicDescription prelocale domain)
  spectrum_iso : Nonempty (SpecDomainIso prelocale domain)
  closed_interpretation_agreement :
    ∃ ρ : ClosedTypeInterpretationAgreement.{u},
      ρ.localicInterpretation σ = prelocale ∧
        ρ.domainInterpretation σ = domain ∧
          Nonempty (LocalicDescription
            (ρ.localicInterpretation σ) (ρ.domainInterpretation σ))

/-- The closed unit type has the expected localic spectrum package once a
closed-type interpretation agreement is supplied.  This isolates the base case
of Theorem 7.3.16 without asserting the missing recursive/product/function-space
constructions for every closed type. -/
theorem closedTypeSpectrumDescription_one_of_agreement
    (ρ : ClosedTypeInterpretationAgreement.{u}) :
    Nonempty (ClosedTypeSpectrumDescription.{u} (.one : ClosedTypeExpr)) := by
  refine ⟨{
    prelocale := punitOpenPrelocale
    domain := punitBifiniteDomain
    property_language := punitPropertyLanguagePrelocale
    prelocale_eq_property_language := rfl
    describes := ⟨punitLocalicDescription⟩
    spectrum_iso := ⟨punitSpecDomainIso⟩
    closed_interpretation_agreement := ?_ }⟩
  refine ⟨ρ, ρ.one_localic_clause, ρ.one_domain_clause, ?_⟩
  rw [ρ.one_localic_clause, ρ.one_domain_clause]
  exact ⟨punitLocalicDescription⟩

/-- Proposition 7.3.3 PDF-facing statement. -/
theorem prop_7_3_3_localic_description_spectrum
    (A : DomainPrelocale.{u}) (D : Chapter4.BifiniteDomain.{u}) :
    Nonempty (LocalicDescription A D) ↔ Nonempty (SpecDomainIso A D) := by
  admit

/-- Concrete data for the duality between domain prelocales and bifinite
domains.  Besides the high-level dual-equivalence package, it records that each
translation is witnessed by a localic description and the corresponding spectrum
isomorphism. -/
structure DomainPrelocaleDuality : Type (u + 1) where
  duality : DualEquivalenceData DomainPrelocale.{u} Chapter4.BifiniteDomain.{u}
  prelocale_to_domain_description :
    ∀ A : DomainPrelocale.{u}, Nonempty (LocalicDescription A (duality.left A))
  domain_to_prelocale_description :
    ∀ D : Chapter4.BifiniteDomain.{u}, Nonempty (LocalicDescription (duality.right D) D)
  prelocale_spectrum_iso :
    ∀ A : DomainPrelocale.{u}, Nonempty (SpecDomainIso A (duality.left A))
  domain_spectrum_iso :
    ∀ D : Chapter4.BifiniteDomain.{u}, Nonempty (SpecDomainIso (duality.right D) D)
  relation_to_scott_map :
    ∀ {A B : DomainPrelocale.{u}},
      JoinApproximablePrelocaleRelation A B →
        BifiniteScottContinuousMap (duality.left B) (duality.left A)
  scott_map_to_relation :
    ∀ {D E : Chapter4.BifiniteDomain.{u}},
      BifiniteScottContinuousMap D E →
        JoinApproximablePrelocaleRelation (duality.right E) (duality.right D)
  relation_scott_inverse_laws : Prop
  scott_relation_inverse_laws : Prop

/-- Theorem 7.3.4 PDF-facing statement. -/
theorem theorem_7_3_4_domain_prelocale_duality :
    Nonempty (DomainPrelocaleDuality.{u}) := by
  admit

/-- Proposition 7.3.6 PDF-facing statement. -/
theorem prop_7_3_6_sub_prelocale_ep_pair
    (A B : DomainPrelocale.{u}) :
    (hAB : SubPrelocale A B) → Nonempty (SpectrumEmbeddingProjection A B hAB) := by
  admit

/-- Corollary 7.3.7 PDF-facing statement. -/
theorem cor_7_3_7_sub_prelocale_domain_embedding
    (A B : DomainPrelocale.{u}) (D E : Chapter4.BifiniteDomain.{u}) :
    (descA : LocalicDescription A D) →
      (descB : LocalicDescription B E) →
        (hAB : SubPrelocale A B) →
          Nonempty (SubPrelocaleDomainEmbedding A B D E descA descB hAB) := by
  admit

/-- Lemma 7.3.8 PDF-facing statement. -/
theorem lemma_7_3_8_compact_open_scott_function_space
    (D E : Chapter4.BifiniteDomain.{u})
    (U : Set (Chapter4.OrderedDomain.ContFunCarrier D.object E.object)) :
    @Chapter2.ScottOpen
        (Chapter4.OrderedDomain.ContFunCarrier D.object E.object)
        (Chapter4.OrderedDomain.contFunPreorder D.object E.object) U ↔
      CompactOpenFunctionSpaceOpen D.object E.object U := by
  admit

/-- Lemma 7.3.9 PDF-facing statement. -/
theorem lemma_7_3_9_bifinite_function_space_compact_opens
    (D E : Chapter4.BifiniteDomain.{u})
    (A : CompactOpenSet D.object) (A' : CompactOpenSet E.object) :
    FunctionSpacePredicateCompactOpen D E A A' := by
  admit

/-- Theorem 7.3.10 PDF-facing statement. -/
theorem theorem_7_3_10_function_space_prelocale
    (A B : DomainPrelocale.{u}) :
    Nonempty (FunctionSpacePrelocaleDescription A B) := by
  admit

/-- Lemma 7.3.11 PDF-facing statement. -/
theorem lemma_7_3_11_plotkin_powerdomain_compact_opens
    (D : Chapter4.BifiniteDomain.{u})
    (O : CompactOpenSet D.object) :
    Nonempty (PlotkinModalCompactOpenPackage D O) := by
  admit

/-- Theorem 7.3.13 PDF-facing representation statement. -/
theorem theorem_7_3_13_plotkin_powerlocale_representation :
    Nonempty (PlotkinPowerlocaleRepresentationData.{u}) := by
  admit

/-- The object-level consequence of Theorem 7.3.13 for a fixed prelocale. -/
theorem theorem_7_3_13_plotkin_powerlocale_description
    (A : DomainPrelocale.{u}) :
    Nonempty (PlotkinPowerlocaleDescription A) := by
  rcases theorem_7_3_13_plotkin_powerlocale_representation with ⟨data⟩
  exact ⟨data.description A⟩

/-- Theorem 7.3.14 PDF-facing statement. -/
theorem theorem_7_3_14_prelocale_chains_bilimits
    (C : PrelocaleChain.{u}) :
    Nonempty (PrelocaleChainBilimitDescription C) := by
  admit

/-- Theorem 7.3.15 PDF-facing statement. -/
theorem theorem_7_3_15_interpretation_preserves_localic_descriptions
    (Var : Type u) :
    ∃ ρ : TypeInterpretationAgreement Var,
      ∀ σ : TypeExpr Var,
        Nonempty (LocalicDescription (ρ.localicInterpretation σ) (ρ.domainInterpretation σ)) := by
  admit

/-- Theorem 7.3.16 PDF-facing statement. -/
theorem theorem_7_3_16_closed_type_expression_spectrum
    (σ : ClosedTypeExpr) :
    Nonempty (ClosedTypeSpectrumDescription.{u} σ) := by
  admit

/-- A decision procedure for the property language following the proof outline:
normalise expressions into finite disjunctions of explicit join-primes, decide
the preorder on primes, and lift the decision to arbitrary expressions. -/
structure PropertyLanguageDecisionProcedure (Var : Type u) where
  Prime : TypeExpr Var → Type u
  prime_expr : ∀ σ : TypeExpr Var, Prime σ → PropertyExpr Var σ
  prime_preorder : ∀ σ : TypeExpr Var, Prime σ → Prime σ → Prop
  prime_preorder_decidable :
    ∀ σ : TypeExpr Var, ∀ p q : Prime σ, Decidable (prime_preorder σ p q)
  expression_preorder : ∀ σ : TypeExpr Var, PropertyExpr Var σ → PropertyExpr Var σ → Prop
  finite_positive_rule_scheme : Prop
  monotone_inductive_definition : Prop
  expression_preorder_refl :
    ∀ σ : TypeExpr Var, ∀ φ : PropertyExpr Var σ, expression_preorder σ φ φ
  expression_preorder_trans :
    ∀ σ : TypeExpr Var, ∀ φ ψ χ : PropertyExpr Var σ,
      expression_preorder σ φ ψ →
        expression_preorder σ ψ χ →
          expression_preorder σ φ χ
  C_predicate : ∀ σ : TypeExpr Var, PropertyExpr Var σ → Prop
  T_predicate : ∀ σ : TypeExpr Var, PropertyExpr Var σ → Prop
  expression_has_finite_construction :
    ∀ σ : TypeExpr Var, ∀ φ : PropertyExpr Var σ, 0 < PropertyExpr.size φ
  prime_is_C :
    ∀ σ : TypeExpr Var, ∀ p : Prime σ, C_predicate σ (prime_expr σ p)
  C_predicate_complete :
    ∀ σ : TypeExpr Var, ∀ φ : PropertyExpr Var σ,
      C_predicate σ φ →
        ∃ p : Prime σ,
          expression_preorder σ φ (prime_expr σ p) ∧
            expression_preorder σ (prime_expr σ p) φ
  normalForm : ∀ σ : TypeExpr Var, PropertyExpr Var σ → List (Prime σ)
  normalForm_sound_complete :
    ∀ σ : TypeExpr Var, ∀ φ : PropertyExpr Var σ,
      let nf := PropertyExpr.finiteDisj ((normalForm σ φ).map (prime_expr σ))
      expression_preorder σ φ nf ∧ expression_preorder σ nf φ
  expression_preorder_decidable :
    ∀ σ : TypeExpr Var, ∀ φ ψ : PropertyExpr Var σ,
      Decidable (expression_preorder σ φ ψ)
  one_preorder_decidable :
    ∀ φ ψ : PropertyExpr Var .one, Decidable (expression_preorder .one φ ψ)
  prime_preorder_structural_reduction :
    ∀ σ : TypeExpr Var, ∀ p q : Prime σ,
      ∃ baseProblems : List (PropertyExpr Var .one × PropertyExpr Var .one),
        prime_preorder σ p q ↔
          ∀ problem : PropertyExpr Var .one × PropertyExpr Var .one,
            problem ∈ baseProblems →
              expression_preorder .one problem.1 problem.2
  prime_preorder_sound_complete :
    ∀ σ : TypeExpr Var, ∀ p q : Prime σ,
      expression_preorder σ (prime_expr σ p) (prime_expr σ q) ↔ prime_preorder σ p q

/-- The property language is decidable through a bundled normal-form decision
procedure. -/
def PropertyLanguageDecidable (Var : Type u) : Prop :=
  Nonempty (PropertyLanguageDecisionProcedure Var)

/-- Theorem 7.3.17 PDF-facing statement. -/
theorem theorem_7_3_17_property_language_decidable
    (Var : Type u) :
    PropertyLanguageDecidable Var := by
  admit

/-- Theorem 7.3.18 PDF-facing statement. -/
theorem theorem_7_3_18_domain_logic_sound_complete
    (Var : Type u) :
    Nonempty (DomainLogicSoundComplete Var) := by
  admit

end Chapter7
end AbramskyJung

import Practice.DomainTheory.Chapter03.NumberedItems.Section31
import Practice.DomainTheory.Chapter03.Section32_Products
import Practice.DomainTheory.Chapter03.Section32_FunctionSpace
import Practice.DomainTheory.Chapter03.Section32_SumsSmashLifting
import Practice.DomainTheory.Chapter03.CategoryNames

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Chapter 3: Section 3.2 wrappers

Book-facing declarations and their local support API are kept together in
textbook dependency order. Reusable constructions remain in the concept-owned
`Chapter03.Section*` modules.
-/

universe u v w z l

namespace AbramskyJung
namespace Chapter3

/-- Proposition 3.2.4(3) support: fixing a point of the right factor makes the
left factor a continuous retract of the product. -/
def prodLeftContinuousSectionRetractionPair
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] (e0 : E) :
    ContinuousSectionRetractionPair D (D × E) where
  s := fun d => (d, e0)
  r := fun p => p.1
  monotone_s := by
    intro x y hxy
    exact ⟨hxy, le_rfl⟩
  monotone_r := by
    intro x y hxy
    exact hxy.1
  retract := by
    intro x
    rfl
  continuous_s := prod_left_section_scottContinuous e0
  continuous_r := prod_fst_scottContinuous

/-- Proposition 3.2.4(3) support: fixing a point of the left factor makes the
right factor a continuous retract of the product. -/
def prodRightContinuousSectionRetractionPair
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] (d0 : D) :
    ContinuousSectionRetractionPair E (D × E) where
  s := fun e => (d0, e)
  r := fun p => p.2
  monotone_s := by
    intro x y hxy
    exact ⟨le_rfl, hxy⟩
  monotone_r := by
    intro x y hxy
    exact hxy.2
  retract := by
    intro x
    rfl
  continuous_s := prod_right_section_scottContinuous d0
  continuous_r := prod_snd_scottContinuous

/-- Proposition 3.2.4(3), reverse direction: a product-continuous domain makes
the left factor continuous once a point of the right factor is chosen. -/
theorem prod_left_continuous_domain_of_product
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (e0 : E) (hProd : IsContinuousDomain (D × E)) :
    IsContinuousDomain D :=
  theorem_3_1_4_retract_continuous_domain_basis
    (prodLeftContinuousSectionRetractionPair (D := D) (E := E) e0) hProd

/-- Proposition 3.2.4(3), reverse direction: a product-continuous domain makes
the right factor continuous once a point of the left factor is chosen. -/
theorem prod_right_continuous_domain_of_product
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (d0 : D) (hProd : IsContinuousDomain (D × E)) :
    IsContinuousDomain E :=
  theorem_3_1_4_retract_continuous_domain_basis
    (prodRightContinuousSectionRetractionPair (D := D) (E := E) d0) hProd

/-- Proposition 3.2.4(3): with chosen points in both factors, product continuity
is equivalent to continuity of each factor.  The explicit points account for the
current Lean `IsDcpo`/domain interface not carrying nonemptiness as a field. -/
theorem prop_3_2_4_product_continuous_domain_iff_of_points
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (d0 : D) (e0 : E) :
    IsContinuousDomain (D × E) ↔ IsContinuousDomain D ∧ IsContinuousDomain E := by
  constructor
  · intro hProd
    exact ⟨prod_left_continuous_domain_of_product e0 hProd,
      prod_right_continuous_domain_of_product d0 hProd⟩
  · intro h
    exact prod_continuous_domain h.1 h.2

/-- Existence of a least element, used to represent pointed dcpo objects without
requiring a global `OrderBot` instance in category-level interfaces. -/
def HasLeastElement (D : Type u) [Preorder D] : Prop :=
  ∃ b : D, Chapter2.IsLeast b

/-- Compatibility name for the shared antisymmetry predicate from Chapter 2. -/
abbrev IsAntisymmetricOrder (D : Type u) [Preorder D] : Prop :=
  Chapter2.IsAntisymmetricOrder D

/-- A map preserves least elements in the unbundled pointed-dcpo interfaces.
This avoids requiring an `OrderBot` instance while still expressing the
bottom-preservation condition of the strict category `DCPO⊥!`. -/
def PreservesLeastElement
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] (f : D → E) : Prop :=
  ∀ x : D, Chapter2.IsLeast x → Chapter2.IsLeast (f x)

/-- Strict Scott-continuous maps for pointed dcpos: Scott-continuity plus
bottom preservation. -/
def StrictScottContinuous
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] (f : D → E) : Prop :=
  ScottContinuous f ∧ PreservesLeastElement f

/-- The strict continuous function-space carrier used for `DCPO⊥!`.
It bundles precisely the strict continuous maps mentioned in Section 3.2.4. -/
structure StrictContFun (D : Type u) (E : Type v) [Preorder D] [Preorder E] where
  toFun : D → E
  continuous : ScottContinuous toFun
  strict : PreservesLeastElement toFun

namespace StrictContFun

instance {D : Type u} {E : Type v} [Preorder D] [Preorder E] :
    CoeFun (StrictContFun D E) (fun _ => D → E) where
  coe f := f.toFun

/-- Pointwise order on strict continuous maps. -/
def Le {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (f g : StrictContFun D E) : Prop :=
  ∀ x : D, f x ≤ g x

instance {D : Type u} {E : Type v} [Preorder D] [Preorder E] :
    Preorder (StrictContFun D E) where
  le := Le
  le_refl f x := le_rfl
  le_trans f g h hfg hgh x := le_trans (hfg x) (hgh x)

/-- Extensionality for bundled strict continuous maps. -/
theorem ext_apply
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    {f g : StrictContFun D E} (h : ∀ x : D, f x = g x) : f = g := by
  cases f with
  | mk f hf hs =>
      cases g with
      | mk g hg gs =>
          have hfun : f = g := funext h
          subst hfun
          congr

end StrictContFun

namespace ContFun

/-- Constant continuous functions, used to exhibit the least element of a
pointed continuous function space. -/
def const {D : Type u} {E : Type v} [Preorder D] [Preorder E] (e : E) : ContFun D E where
  toFun := fun _ => e
  continuous := const_scottContinuous e

/-- If the codomain has a least element, then the constant-bottom function is
least in the pointwise order. -/
theorem const_isLeast
    {D : Type u} {E : Type v} [Preorder D] [Preorder E] {e : E}
    (he : Chapter2.IsLeast e) :
    Chapter2.IsLeast (ContFun.const (D := D) e) := by
  intro f x
  exact he (f x)

/-- A pointed codomain makes the continuous function space pointed by the
constant least function. -/
theorem hasLeastElement_of_codomain
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : HasLeastElement E) : HasLeastElement (ContFun D E) := by
  rcases hE with ⟨e, he⟩
  exact ⟨ContFun.const (D := D) e, ContFun.const_isLeast he⟩

/-- Antisymmetry of the codomain transfers to the pointwise order on continuous
functions. -/
theorem antisymmetric_of_codomain
    {D : Type u} {E : Type v} [Preorder D] [Preorder E]
    (hE : IsAntisymmetricOrder E) : IsAntisymmetricOrder (ContFun D E) := by
  intro f g hfg hgf
  cases f with
  | mk f hf =>
      cases g with
      | mk g hg =>
          have hfun : f = g := funext fun x => hE (f x) (g x) (hfg x) (hgf x)
          subst hfun
          congr

end ContFun

/-- Exact object predicates for the named categories used in Sections 3.2 and
3.3.  Every dcpo object carries antisymmetry; continuous and algebraic variants
also retain their defining basis property.  Strictness belongs to morphisms, so
it does not change the pointed object predicate. -/
def DomainCategoryObject (C : DomainCategoryName) (D : Type u) [Preorder D] : Prop :=
  match C with
  | DomainCategoryName.DCPO => IsDcpo D ∧ IsAntisymmetricOrder D
  | DomainCategoryName.DCPO_bot =>
      IsDcpo D ∧ IsAntisymmetricOrder D ∧ HasLeastElement D
  | DomainCategoryName.DCPO_bot_strict =>
      IsDcpo D ∧ IsAntisymmetricOrder D ∧ HasLeastElement D
  | DomainCategoryName.CONT =>
      IsDcpo D ∧ IsAntisymmetricOrder D ∧ IsContinuousDomain D
  | DomainCategoryName.ALG =>
      IsDcpo D ∧ IsAntisymmetricOrder D ∧ IsAlgebraicDomain D
  | DomainCategoryName.CONT_bot =>
      IsDcpo D ∧ IsAntisymmetricOrder D ∧ IsContinuousDomain D ∧ HasLeastElement D
  | DomainCategoryName.ALG_bot =>
      IsDcpo D ∧ IsAntisymmetricOrder D ∧ IsAlgebraicDomain D ∧ HasLeastElement D
  | DomainCategoryName.CONT_bot_strict =>
      IsDcpo D ∧ IsAntisymmetricOrder D ∧ IsContinuousDomain D ∧ HasLeastElement D
  | DomainCategoryName.ALG_bot_strict =>
      IsDcpo D ∧ IsAntisymmetricOrder D ∧ IsAlgebraicDomain D ∧ HasLeastElement D

/-- Lightweight order-isomorphism data for categorical comparison objects.
This keeps the Section 3.2 interfaces stronger than a bare carrier equivalence
without importing a full category-theory development. -/
structure OrderIsoData (A : Type u) (B : Type v) [Preorder A] [Preorder B] where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ x : A, invFun (toFun x) = x
  right_inv : ∀ y : B, toFun (invFun y) = y
  monotone_to : Monotone toFun
  monotone_inv : Monotone invFun

/-- Identity order-isomorphism data. -/
def OrderIsoData.refl (A : Type u) [Preorder A] : OrderIsoData A A where
  toFun := id
  invFun := id
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  monotone_to := by intro x y hxy; exact hxy
  monotone_inv := by intro x y hxy; exact hxy

/-- Lemma 3.2.5 full-subcategory interface.

The local category model uses an object predicate and inherited
Scott-continuous hom-sets.  Finite products are represented by a terminal
object and binary products with projections, pairing and uniqueness laws; an
arbitrary object closed under a type-valued operation is not enough.  The PDF
attributes the resulting comparison theorem to Smyth [Smy83a] and Jung
[Jun89]. -/
structure FullSubcategoryWithFiniteProducts (Ambient : DomainCategoryName) : Type (u + 1) where
  ambient_supported :
    Ambient = DomainCategoryName.DCPO ∨ Ambient = DomainCategoryName.DCPO_bot_strict
  object : ∀ D : Type u, [Preorder D] → Prop
  object_in_ambient :
    ∀ D : Type u, ∀ [Preorder D], object D → DomainCategoryObject Ambient D
  product :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      object D → object E → Type u
  product_preorder :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      ∀ hD : object D, ∀ hE : object E, Preorder (product D E hD hE)
  product_object :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      ∀ hD : object D, ∀ hE : object E,
        @object (product D E hD hE) (product_preorder D E hD hE)
  terminal : Type u
  terminal_preorder : Preorder terminal
  terminal_object : @object terminal terminal_preorder
  terminate :
    ∀ X : Type u, ∀ [Preorder X], ∀ _hX : object X,
      @ContFun X terminal inferInstance terminal_preorder
  terminate_unique :
    ∀ X : Type u, ∀ [Preorder X], ∀ hX : object X,
      ∀ f : @ContFun X terminal inferInstance terminal_preorder,
        f = terminate X hX
  fst :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      ∀ hD : object D, ∀ hE : object E,
        @ContFun (product D E hD hE) D (product_preorder D E hD hE) inferInstance
  snd :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      ∀ hD : object D, ∀ hE : object E,
        @ContFun (product D E hD hE) E (product_preorder D E hD hE) inferInstance
  lift :
    ∀ X D E : Type u, ∀ [Preorder X], ∀ [Preorder D], ∀ [Preorder E],
      ∀ _hX : object X, ∀ hD : object D, ∀ hE : object E,
        ContFun X D → ContFun X E →
          @ContFun X (product D E hD hE) inferInstance (product_preorder D E hD hE)
  lift_fst :
    ∀ X D E : Type u, ∀ [Preorder X], ∀ [Preorder D], ∀ [Preorder E],
      ∀ hX : object X, ∀ hD : object D, ∀ hE : object E,
        ∀ f : ContFun X D, ∀ g : ContFun X E,
          ContFun.comp (fst D E hD hE) (lift X D E hX hD hE f g) = f
  lift_snd :
    ∀ X D E : Type u, ∀ [Preorder X], ∀ [Preorder D], ∀ [Preorder E],
      ∀ hX : object X, ∀ hD : object D, ∀ hE : object E,
        ∀ f : ContFun X D, ∀ g : ContFun X E,
          ContFun.comp (snd D E hD hE) (lift X D E hX hD hE f g) = g
  lift_unique :
    ∀ X D E : Type u, ∀ [Preorder X], ∀ [Preorder D], ∀ [Preorder E],
      ∀ hX : object X, ∀ hD : object D, ∀ hE : object E,
        ∀ f : ContFun X D, ∀ g : ContFun X E,
          ∀ h : @ContFun X (product D E hD hE) inferInstance (product_preorder D E hD hE),
            ContFun.comp (fst D E hD hE) h = f →
              ContFun.comp (snd D E hD hE) h = g →
                h = lift X D E hX hD hE f g

/-- Lemma 3.2.5 conclusion for the object-predicate full-subcategory interface:
every chosen finite-product object is represented together with an
order-isomorphism to the explicit cartesian product. -/
def FullSubcategoryFiniteProductsAgreeWithCartesian
    (Ambient : DomainCategoryName) (Sub : FullSubcategoryWithFiniteProducts.{u} Ambient) : Prop :=
  ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
    ∀ hD : Sub.object D, ∀ hE : Sub.object E,
      Nonempty (@OrderIsoData (Sub.product D E hD hE) (CartesianProduct D E)
        (Sub.product_preorder D E hD hE) inferInstance)

/-- Lemma 3.2.5, object-predicate full-subcategory form. The PDF refers to
Smyth [Smy83a] and Jung [Jun89]; the located general source is Jung [Jun89],
Lemma 1.21(ii). The axiom is the visible boundary between that categorical
comparison theorem and this project's local full-subcategory interface. -/
axiom lemma_3_2_5_full_subcategory_products_cartesian_full
    (Ambient : DomainCategoryName)
    (Sub : FullSubcategoryWithFiniteProducts.{u} Ambient) :
    FullSubcategoryFiniteProductsAgreeWithCartesian.{u} Ambient Sub

/-- Lemma 3.2.5 interface. PDF text: "Let C be a full subcategory of DCPO or
DCPO⊥! which has finite products. Then these are isomorphic to the cartesian
product."

Current Lean spelling: this legacy wrapper specializes the object-predicate
full-subcategory interface above to a named ambient object class.  A
finite-product structure is represented by a chosen binary product object.  The
comparison with the explicit cartesian product is recorded below as the
documented Smyth/Jung external theorem, not as a preloaded field. -/
structure HasFiniteProducts (C : DomainCategoryName) : Type (u + 1) where
  data : FullSubcategoryWithFiniteProducts.{u} C
  object_eq : ∀ D : Type u, ∀ [Preorder D], data.object D ↔ DomainCategoryObject C D

/-- Lemma 3.2.5 conclusion in the current interface: every chosen finite-product
object is represented together with an order-isomorphism to the explicit
cartesian product. -/
def FiniteProductsAgreeWithCartesian
    (_C : DomainCategoryName) (hC : HasFiniteProducts.{u} _C) : Prop :=
  ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
    ∀ hD : hC.data.object D, ∀ hE : hC.data.object E,
      Nonempty (@OrderIsoData (hC.data.product D E hD hE) (CartesianProduct D E)
        (hC.data.product_preorder D E hD hE) inferInstance)

/-- Lemma 3.2.5, legacy named-category interface form, derived from the
documented object-predicate external theorem above. -/
theorem lemma_3_2_5_full_subcategory_products_cartesian
    (C : DomainCategoryName) (hC : HasFiniteProducts.{u} C) :
    FiniteProductsAgreeWithCartesian.{u} C hC := by
  simpa [FiniteProductsAgreeWithCartesian,
    FullSubcategoryFiniteProductsAgreeWithCartesian] using
    (lemma_3_2_5_full_subcategory_products_cartesian_full C hC.data)

/-- Separate Scott-continuity of a binary map. -/
def SeparatelyScottContinuous
    {D : Type u} {E : Type v} {F : Type w} [Preorder D] [Preorder E] [Preorder F]
    (f : D × E → F) : Prop :=
  (∀ d : D, ScottContinuous (fun e : E => f (d, e))) ∧
    ∀ e : E, ScottContinuous (fun d : D => f (d, e))

/-- Lemma 3.2.6. PDF text: "A function f : D × E -> F is continuous if and
only if it is continuous in each variable separately."

Lean spelling: binary Scott-continuity for the product preorder is equivalent
to Scott-continuity of every coordinate section. -/
theorem lemma_3_2_6_continuous_iff_separately_continuous
    {D : Type u} {E : Type v} {F : Type w} [Preorder D] [Preorder E] [Preorder F]
    (f : D × E → F) :
    ScottContinuous f ↔ SeparatelyScottContinuous f := by
  constructor
  · intro hf
    constructor
    · intro d
      constructor
      · intro e₁ e₂ he
        exact hf.1 ⟨le_rfl, he⟩
      · intro A s hA hs
        let B : Set (D × E) := {p | p.1 = d ∧ p.2 ∈ A}
        have hBdir : DirectedSet B := by
          constructor
          · rcases hA.1 with ⟨a, ha⟩
            exact ⟨(d, a), rfl, ha⟩
          · intro p hp q hq
            rcases hA.2 hp.2 hq.2 with ⟨r, hr, hpr, hqr⟩
            exact ⟨(d, r), ⟨rfl, hr⟩, ⟨by simpa [hp.1], hpr⟩,
              ⟨by simpa [hq.1], hqr⟩⟩
        have hBsup : IsSup B (d, s) := by
          constructor
          · intro p hp
            exact ⟨by simpa [hp.1], hs.1 hp.2⟩
          · intro q hq
            constructor
            · rcases hA.1 with ⟨a, ha⟩
              exact (hq (a := (d, a)) ⟨rfl, ha⟩).1
            · exact hs.2 q.2 (by
                intro a ha
                exact (hq (a := (d, a)) ⟨rfl, ha⟩).2)
        have hfB : IsSup (f '' B) (f (d, s)) := hf.2 hBdir hBsup
        constructor
        · intro y hy
          rcases hy with ⟨a, ha, rfl⟩
          exact hfB.1 ⟨(d, a), ⟨rfl, ha⟩, rfl⟩
        · intro y hy
          exact hfB.2 y (by
            intro z hz
            rcases hz with ⟨p, hp, rfl⟩
            rcases p with ⟨pd, pe⟩
            rcases hp with ⟨hpd, hpA⟩
            have hpd' : pd = d := by simpa using hpd
            rw [hpd']
            exact hy ⟨pe, by simpa using hpA, rfl⟩)
    · intro e
      constructor
      · intro d₁ d₂ hd
        exact hf.1 ⟨hd, le_rfl⟩
      · intro A s hA hs
        let B : Set (D × E) := {p | p.1 ∈ A ∧ p.2 = e}
        have hBdir : DirectedSet B := by
          constructor
          · rcases hA.1 with ⟨a, ha⟩
            exact ⟨(a, e), ha, rfl⟩
          · intro p hp q hq
            rcases hA.2 hp.1 hq.1 with ⟨r, hr, hpr, hqr⟩
            exact ⟨(r, e), ⟨hr, rfl⟩, ⟨hpr, by simpa [hp.2]⟩,
              ⟨hqr, by simpa [hq.2]⟩⟩
        have hBsup : IsSup B (s, e) := by
          constructor
          · intro p hp
            exact ⟨hs.1 hp.1, by simpa [hp.2]⟩
          · intro q hq
            constructor
            · exact hs.2 q.1 (by
                intro a ha
                exact (hq (a := (a, e)) ⟨ha, rfl⟩).1)
            · rcases hA.1 with ⟨a, ha⟩
              exact (hq (a := (a, e)) ⟨ha, rfl⟩).2
        have hfB : IsSup (f '' B) (f (s, e)) := hf.2 hBdir hBsup
        constructor
        · intro y hy
          rcases hy with ⟨a, ha, rfl⟩
          exact hfB.1 ⟨(a, e), ⟨ha, rfl⟩, rfl⟩
        · intro y hy
          exact hfB.2 y (by
            intro z hz
            rcases hz with ⟨p, hp, rfl⟩
            rcases p with ⟨pd, pe⟩
            rcases hp with ⟨hpA, hpe⟩
            have hpe' : pe = e := by simpa using hpe
            rw [hpe']
            exact hy ⟨pd, by simpa using hpA, rfl⟩)
  · intro hsep
    have hmono : Monotone f := by
      intro p q hpq
      exact le_trans ((hsep.2 p.2).1 hpq.1) ((hsep.1 q.1).1 hpq.2)
    constructor
    · exact hmono
    · intro A s hA hs
      let AD : Set D := {d | ∃ e : E, (d, e) ∈ A}
      let AE : Set E := {e | ∃ d : D, (d, e) ∈ A}
      have hADdir : DirectedSet AD := by
        constructor
        · rcases hA.1 with ⟨p, hp⟩
          exact ⟨p.1, p.2, hp⟩
        · intro d hd d' hd'
          rcases hd with ⟨e, hde⟩
          rcases hd' with ⟨e', hd'e'⟩
          rcases hA.2 hde hd'e' with ⟨p, hp, hdp, hd'p⟩
          exact ⟨p.1, ⟨p.2, hp⟩, hdp.1, hd'p.1⟩
      have hAEdir : DirectedSet AE := by
        constructor
        · rcases hA.1 with ⟨p, hp⟩
          exact ⟨p.2, p.1, hp⟩
        · intro e he e' he'
          rcases he with ⟨d, hde⟩
          rcases he' with ⟨d', hd'e'⟩
          rcases hA.2 hde hd'e' with ⟨p, hp, hdp, hd'p⟩
          exact ⟨p.2, ⟨p.1, hp⟩, hdp.2, hd'p.2⟩
      have hAEsup : IsSup AE s.2 := by
        constructor
        · intro e he
          rcases he with ⟨d, hde⟩
          exact (hs.1 hde).2
        · intro e he
          have hUpper : IsUpperBound A (s.1, e) := by
            intro p hp
            exact ⟨(hs.1 hp).1, he ⟨p.1, hp⟩⟩
          exact (hs.2 (s.1, e) hUpper).2
      have hADsup : IsSup AD s.1 := by
        constructor
        · intro d hd
          rcases hd with ⟨e, hde⟩
          exact (hs.1 hde).1
        · intro d hd
          have hUpper : IsUpperBound A (d, s.2) := by
            intro p hp
            exact ⟨hd ⟨p.2, hp⟩, (hs.1 hp).2⟩
          exact (hs.2 (d, s.2) hUpper).1
      constructor
      · intro z hz
        rcases hz with ⟨p, hp, rfl⟩
        exact hmono (hs.1 hp)
      · intro y hy
        have hy_d_snd : ∀ d ∈ AD, f (d, s.2) ≤ y := by
          intro d hd
          have hSupE : IsSup ((fun e : E => f (d, e)) '' AE) (f (d, s.2)) :=
            (hsep.1 d).2 hAEdir hAEsup
          exact hSupE.2 y (by
            intro z hz
            rcases hz with ⟨e, he, rfl⟩
            rcases hd with ⟨ed, hdA⟩
            rcases he with ⟨d', hd'eA⟩
            rcases hA.2 hdA hd'eA with ⟨p, hp, hdp, hd'p⟩
            exact le_trans (hmono ⟨hdp.1, hd'p.2⟩) (hy ⟨p, hp, rfl⟩))
        have hSupD : IsSup ((fun d : D => f (d, s.2)) '' AD) (f (s.1, s.2)) :=
          (hsep.2 s.2).2 hADdir hADsup
        exact hSupD.2 y (by
          intro z hz
          rcases hz with ⟨d, hd, rfl⟩
          exact hy_d_snd d hd)

/-- Lemma 3.2.7 full-subcategory interface.

This is the object-predicate version of "a cartesian closed full subcategory of
`DCPO`".  Morphisms are inherited Scott-continuous maps, finite products carry
their actual universal properties, and `exponential_universal` records the
hom-order isomorphism characterizing exponentials.  The external comparison
theorem below follows the PDF's Smyth/Jung reference. -/
structure CartesianClosedFullSubcategoryOfDCPO : Type (u + 1) where
  object : ∀ D : Type u, [Preorder D] → Prop
  object_dcpo : ∀ D : Type u, ∀ [Preorder D], object D → IsDcpo D
  object_antisymmetric : ∀ D : Type u, ∀ [Preorder D], object D → IsAntisymmetricOrder D
  function_space_dcpo :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      object D → object E → IsDcpo (ContFun D E)
  function_space_antisymmetric :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      object D → object E → IsAntisymmetricOrder (ContFun D E)
  exponential :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      object D → object E → Type u
  exponential_preorder :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      ∀ hD : object D, ∀ hE : object E, Preorder (exponential D E hD hE)
  exponential_object :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      ∀ hD : object D, ∀ hE : object E,
        @object (exponential D E hD hE) (exponential_preorder D E hD hE)
  exponential_dcpo :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      ∀ hD : object D, ∀ hE : object E,
        @IsDcpo (exponential D E hD hE) (exponential_preorder D E hD hE)
  exponential_antisymmetric :
    ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
      ∀ hD : object D, ∀ hE : object E,
        @IsAntisymmetricOrder (exponential D E hD hE) (exponential_preorder D E hD hE)
  products : FullSubcategoryWithFiniteProducts.{u} DomainCategoryName.DCPO
  products_object_iff :
    ∀ D : Type u, ∀ [Preorder D], products.object D ↔ object D
  exponential_universal :
    ∀ X D E : Type u, ∀ [Preorder X], ∀ [Preorder D], ∀ [Preorder E],
      ∀ hX : object X, ∀ hD : object D, ∀ hE : object E,
        Nonempty
          (@OrderIsoData
            (@ContFun
              (products.product X D ((products_object_iff X).2 hX)
                ((products_object_iff D).2 hD)) E
              (products.product_preorder X D ((products_object_iff X).2 hX)
                ((products_object_iff D).2 hD)) inferInstance)
            (@ContFun X (exponential D E hD hE) inferInstance
              (exponential_preorder D E hD hE))
            inferInstance inferInstance)

/-- Lemma 3.2.7 conclusion for the object-predicate full-subcategory interface:
each exponential object is a partial-order dcpo and is order-isomorphic to the
Scott-continuous function-space carrier.  The comparison is supplied by the
documented external theorem below from the stated exponential universal
property. -/
def FullSubcategoryExponentialAgreesWithFunctionSpace
    (C : CartesianClosedFullSubcategoryOfDCPO.{u}) : Prop :=
  ∀ D E : Type u, ∀ [Preorder D], ∀ [Preorder E],
    ∀ hD : C.object D, ∀ hE : C.object E,
      Nonempty (@OrderIsoData (C.exponential D E hD hE) (ContFun D E)
        (C.exponential_preorder D E hD hE) inferInstance)

/-- Lemma 3.2.7, object-predicate full-subcategory form. The preceding textbook
discussion refers back to Smyth [Smy83a]; the located general source is Jung
[Jun89], Lemma 1.21(iii). The axiom is the visible bridge from that categorical
comparison theorem to the local universal-property interface. -/
axiom lemma_3_2_7_exponential_is_function_space_full
    (C : CartesianClosedFullSubcategoryOfDCPO.{u}) :
    FullSubcategoryExponentialAgreesWithFunctionSpace.{u} C

/-- Named-category compatibility wrapper for the full cartesian-closed
subcategory interface.  Unlike the former carrier-only record, `data` includes
finite-product and exponential universal properties. -/
structure CartesianClosedFullSubcategory (C : DomainCategoryName) : Type (u + 1) where
  ambient_eq : C = DomainCategoryName.DCPO
  data : CartesianClosedFullSubcategoryOfDCPO.{u}
  object_iff :
    ∀ D : Type u, ∀ [Preorder D], data.object D ↔ DomainCategoryObject C D

/-- Lemma 3.2.7 conclusion in the current interface: every chosen exponential
object is represented as a partial-order dcpo together with an order-isomorphism
to the bundled Scott-continuous function-space carrier, which is also recorded
as a partial-order dcpo. -/
def ExponentialAgreesWithFunctionSpace
    (_C : DomainCategoryName) (hC : CartesianClosedFullSubcategory.{u} _C) : Prop :=
  FullSubcategoryExponentialAgreesWithFunctionSpace hC.data

/-- Lemma 3.2.7, legacy named-category interface form, derived from the
documented object-predicate external theorem above. -/
theorem lemma_3_2_7_exponential_is_function_space
    (C : DomainCategoryName) (hC : CartesianClosedFullSubcategory.{u} C) :
    ExponentialAgreesWithFunctionSpace.{u} C hC := by
  simpa [ExponentialAgreesWithFunctionSpace,
    FullSubcategoryExponentialAgreesWithFunctionSpace] using
    (lemma_3_2_7_exponential_is_function_space_full hC.data)

/-- Proposition 3.2.8. PDF text: "The coalesced sum of pointed dcpo's is a
pointed dcpo."

Current Lean spelling: the coalesced-sum carrier is a dcpo with least bottom.
The explicit bottom-separation hypotheses record the poset fact that no
non-bottom element can be below bottom in the current preorder-based interface. -/
theorem prop_3_2_8_coalesced_sum_pointed_dcpo
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hD : IsDcpo D) (hE : IsDcpo E)
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    IsDcpo (CoalescedSum D E) ∧ Chapter2.IsLeast (⊥ : CoalescedSum D E) :=
  CoalescedSum.pointedDcpo (D := D) (E := E) hD hE hDbot hEbot

/-- The strict coproduct universal-property interface for the coalesced sum, at
the carrier level with strict bottom-preserving maps. -/
def IsStrictCoproduct
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E] :
    Prop :=
  Nonempty (CoalescedSum.StrictCoproductData.{u, v, w} (D := D) (E := E))

/-- The strict Scott-continuous coproduct interface for the coalesced sum.  This
is the `DCPO⊥!` part of Proposition 3.2.9 in the current unbundled interface:
strict injections are Scott-continuous, and strict Scott-continuous pairs have
a unique strict mediator whose underlying map is Scott-continuous. -/
def IsStrictContinuousCoproduct
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    Prop :=
  Nonempty
    (CoalescedSum.StrictContinuousCoproductData.{u, v, w} (D := D) (E := E)
      hDbot hEbot)

/-- The `CONT⊥!` object-class part of Proposition 3.2.9.  The local predicate
`IsContinuousDomain` records the basis property, so the dcpo parts of the object
class are stated explicitly. -/
def CoalescedSumContinuousObjectClosure
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (_hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (_hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    Prop :=
  IsDcpo D → IsDcpo E → IsContinuousDomain D → IsContinuousDomain E →
    IsDcpo (CoalescedSum D E) ∧ IsContinuousDomain (CoalescedSum D E)

/-- The `ALG⊥!` object-class part of Proposition 3.2.9, isolated as an explicit
closure clause.  The local predicate `IsAlgebraicDomain` records the compact
basis property, so the dcpo parts of the object class are stated explicitly. -/
def CoalescedSumAlgebraicObjectClosure
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (_hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (_hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    Prop :=
  IsDcpo D → IsDcpo E → IsAlgebraicDomain D → IsAlgebraicDomain E →
    IsDcpo (CoalescedSum D E) ∧ IsAlgebraicDomain (CoalescedSum D E)

/-- Proposition 3.2.9 support: the coalesced sum preserves the `CONT⊥!` object
class in the current preorder interface. -/
theorem coalescedSumContinuousObjectClosure
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    CoalescedSumContinuousObjectClosure D E hDbot hEbot := by
  intro hDdcpo hEdcpo hDcont hEcont
  exact
    ⟨CoalescedSum.isDcpo (D := D) (E := E) hDdcpo hEdcpo hDbot hEbot,
      CoalescedSum.continuousDomain (D := D) (E := E) hDbot hEbot hDcont hEcont⟩

/-- Proposition 3.2.9 support: the coalesced sum preserves the `ALG⊥!` object
class in the current preorder interface. -/
theorem coalescedSumAlgebraicObjectClosure
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    CoalescedSumAlgebraicObjectClosure D E hDbot hEbot := by
  intro hDdcpo hEdcpo hDalg hEalg
  exact
    ⟨CoalescedSum.isDcpo (D := D) (E := E) hDdcpo hEdcpo hDbot hEbot,
      CoalescedSum.algebraicDomain (D := D) (E := E) hDbot hEbot hDalg hEalg⟩

/-- Full Proposition 3.2.9 data in the current interface: the proved
`DCPO⊥!` strict continuous coproduct core, plus proved object-class closure
clauses for `CONT⊥!` and `ALG⊥!`. -/
structure CoalescedSumFullCoproductData
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) : Prop where
  dcpo_coproduct : IsStrictContinuousCoproduct.{u, v, w} D E hDbot hEbot
  continuous_object_closure : CoalescedSumContinuousObjectClosure D E hDbot hEbot
  algebraic_object_closure : CoalescedSumAlgebraicObjectClosure D E hDbot hEbot

/-- Proposition 3.2.9. PDF text: "The coalesced sum of pointed dcpo's is the
coproduct in DCPO⊥!, CONT⊥!, and ALG⊥!."

Current Lean spelling: this declaration records the `DCPO⊥!` strict continuous
coproduct core: strict Scott-continuous injections and the expected unique
strict Scott-continuous mediator for every pair of strict Scott-continuous maps.
The full data declaration below adds the `CONT⊥!` and `ALG⊥!` object-class
preservation clauses, with the same bottom-separation hypotheses used by the
coalesced-sum dcpo construction in the preorder interface. -/
noncomputable def prop_3_2_9_coalesced_sum_coproduct
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    IsStrictContinuousCoproduct.{u, v, w} D E hDbot hEbot :=
  ⟨CoalescedSum.strictContinuousCoproductData (D := D) (E := E) hDbot hEbot⟩

/-- Proposition 3.2.9, full-data packaging for the current interface. -/
noncomputable def prop_3_2_9_coalesced_sum_coproduct_full
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    CoalescedSumFullCoproductData D E hDbot hEbot :=
  { dcpo_coproduct := prop_3_2_9_coalesced_sum_coproduct D E hDbot hEbot
    continuous_object_closure := coalescedSumContinuousObjectClosure D E hDbot hEbot
    algebraic_object_closure := coalescedSumAlgebraicObjectClosure D E hDbot hEbot }

/-- Proposition 3.2.9, theorem-facing existence wrapper around the complete
coproduct and object-class preservation package. -/
theorem prop_3_2_9_coalesced_sum_coproduct_full_exists
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥) :
    Nonempty (CoalescedSumFullCoproductData D E hDbot hEbot) :=
  ⟨prop_3_2_9_coalesced_sum_coproduct_full D E hDbot hEbot⟩

/-- Proposition 3.2.9, full-data packaging from explicit object-class closure
proofs.  This compatibility constructor is retained for callers that already
package the object-class closure clauses separately. -/
noncomputable def prop_3_2_9_coalesced_sum_coproduct_full_of_object_closure
    (D : Type u) (E : Type v) [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]
    (hDbot : ∀ x : D, x ≤ ⊥ → x = ⊥)
    (hEbot : ∀ y : E, y ≤ ⊥ → y = ⊥)
    (hCont : CoalescedSumContinuousObjectClosure D E hDbot hEbot)
    (hAlg : CoalescedSumAlgebraicObjectClosure D E hDbot hEbot) :
    CoalescedSumFullCoproductData D E hDbot hEbot :=
  { dcpo_coproduct := prop_3_2_9_coalesced_sum_coproduct D E hDbot hEbot
    continuous_object_closure := hCont
    algebraic_object_closure := hAlg }


end Chapter3
end AbramskyJung

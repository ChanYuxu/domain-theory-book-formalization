import Practice.DomainTheory.Chapter05.Core

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Section 5.1

Functor algebras and the isomorphism property of initial algebras.

The initial-algebra isomorphism is proved from initiality and the functor laws,
following the argument printed on PDF pages 69--70.
-/

universe u

namespace AbramskyJung
namespace Chapter5

open Chapter4

/-- Definition 5.1.1, algebra part.  PDF text: an `F`-algebra is an object `A`
and a map `f : F A -> A`.  Here this is specialized to the local
`DomainEndofunctor` interface on bundled ordered domains. -/
abbrev def_5_1_1_functor_algebra (F : DomainEndofunctor.{u}) : Type (u + 1) :=
  FunctorAlgebra F

/-- Definition 5.1.1, homomorphism part.  PDF text: a homomorphism between
`f : F A -> A` and `f' : F A' -> A'` is a map `g : A -> A'` such that
`g ∘ f = f' ∘ F g`.  The commuting square is the `commutes` field of
`FunctorAlgebra.Hom`. -/
abbrev def_5_1_1_functor_algebra_hom
    (F : DomainEndofunctor.{u}) (A B : FunctorAlgebra F) : Type u :=
  FunctorAlgebra.Hom F A B

/-- Lemma 5.1.2.  PDF text: if `i : F(A) -> A` is an initial `F`-algebra, then
`i` is an isomorphism.

The proof constructs the unique homomorphism `f : A → F(A)`, uses initiality
to obtain `i ∘ f = id`, and then uses functoriality and the homomorphism square
to obtain `f ∘ i = id`. -/
theorem lemma_5_1_2_initial_algebra_structure_is_iso
    (F : DomainEndofunctor.{u}) (A : FunctorAlgebra F)
    (hA : FunctorAlgebra.IsInitial F A) :
    FunctorAlgebra.HasStructureIso F A := by
  rcases hA.unique_hom (FunctorAlgebra.mapAlgebra F A) with ⟨f, _hfUnique⟩
  rcases hA.unique_hom A with ⟨h, hhUnique⟩
  let i : FunctorAlgebra.Hom F (FunctorAlgebra.mapAlgebra F A) A :=
    FunctorAlgebra.structureHom F A
  let iCompF : FunctorAlgebra.Hom F A A :=
    FunctorAlgebra.compHom F i f
  have hiCompF : ∀ x : A.object.carrier, iCompF.map x = x := by
    intro x
    calc
      iCompF.map x = h.map x := hhUnique iCompF x
      _ = (FunctorAlgebra.idHom F A).map x := (hhUnique (FunctorAlgebra.idHom F A) x).symm
      _ = x := rfl
  refine ⟨⟨f.map, ?_, ?_⟩⟩
  · exact hiCompF
  · intro x
    calc
      f.map (A.structureMap x) =
          F.mapHom A.structureMap (F.mapHom f.map x) := f.commutes x
      _ = F.mapHom (OrderedDomain.compContFun A.structureMap f.map) x :=
        F.mapHom_comp f.map A.structureMap x
      _ = F.mapHom (OrderedDomain.idContFun A.object) x := by
        apply F.mapHom_congr
        exact hiCompF
      _ = x := F.mapHom_id x

end Chapter5
end AbramskyJung

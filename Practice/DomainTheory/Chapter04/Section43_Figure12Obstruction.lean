import Practice.DomainTheory.Chapter04.Section43_FunctionSpaceSupport

set_option autoImplicit false

/-!
# The Figure 12 function-space obstruction for Lemma 4.3.1

This module isolates the exact unresolved boundary in source Case 1.
-/

universe u

namespace AbramskyJung
namespace Chapter4

/-- Source Case 1, isolated at its exact remaining proof boundary.  The book's
formula requires a successor operation on the possibly ordinal descending chain
and claims a pointwise supremum while leaving the family equal to `g` outside
the intersection.  `Figure12ADiagram` records only the displayed order, so these
claims cannot yet be reconstructed without adding and source-validating further
chain data. -/
theorem not_continuous_functionSpace_of_figure12
    (D A : OrderedDomain.{u}) (hD : IsContinuousDomainObject D)
    (hNotCoherent : ¬ IsCoherentDomain D)
    (hA : Figure12ADiagram A) (hAdcpo : Chapter3.IsDcpo A.carrier) :
    ¬ Chapter3.IsContinuousDomain (Chapter3.ContFun D.carrier A.carrier) := by
  sorry

end Chapter4
end AbramskyJung

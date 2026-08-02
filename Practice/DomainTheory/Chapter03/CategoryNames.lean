import Practice.DomainTheory.Chapter03.Prelude

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
# Abramsky--Jung, Domain Theory, Chapter 3 category names
-/

namespace AbramskyJung
namespace Chapter3

/-- The category names in Section 3.2 are represented here as predicates on objects. -/
inductive DomainCategoryName where
  | DCPO
  | DCPO_bot
  | DCPO_bot_strict
  | CONT
  | ALG
  | CONT_bot
  | ALG_bot
  | CONT_bot_strict
  | ALG_bot_strict

end Chapter3
end AbramskyJung

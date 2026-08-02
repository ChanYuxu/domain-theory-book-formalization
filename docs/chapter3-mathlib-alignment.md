# Chapter 3 mathlib Alignment Audit

Audit date: 2026-07-29

Scope: all 38 mapped textbook declarations in `docs/chapter3-map.json`.

Those items contain 127 mapped Lean-name references. Each mapped name is
covered by its source item's classification below. Unmapped proof helpers and
the public/private boundary of the 5,810-line `NumberedItems.lean` file require
a separate API-surface and module-ownership audit.

Project baseline:

- Lean: `leanprover/lean4:v4.30.0-rc2`
- mathlib release: `v4.30.0-rc2`
- mathlib commit: `5450b53e5ddc75d46418fabb605edbf36bd0beb6`
- chapter build target: `Practice.DomainTheory.Chapter03.NumberedItems`

This report compares the source-exact textbook wrappers with the pinned
mathlib source. It is not a human approval record. "No counterpart found"
means no matching declaration was found in that checkout; it does not assert
that the mathematical result is new.

## Classification

- `direct`: mathlib already has the required semantics and can implement the
  textbook wrapper directly.
- `bridge`: the semantics agree, but a proved conversion is needed because of
  representation, bundling, or orientation.
- `partial`: mathlib supplies a specialization or substantial infrastructure,
  but not the complete textbook declaration.
- `absent`: no matching declaration was found in the pinned mathlib.

An item containing several declarations is assigned its most conservative
applicable class. Mixed cases are identified explicitly in the action column.

## Executive Findings

1. The local `Adjunction l u` is the order-theoretic notion already represented
   by mathlib's `GaloisConnection l u`; only the orientation of the displayed
   equivalence is reversed. The local preliminary, unit/counit, preservation,
   and image laws should become textbook wrappers around the mature
   `GaloisConnection`, `GaloisInsertion`, and `GaloisCoinsertion` APIs.
   Mathlib also provides `GaloisConnection.adjunction`, which promotes this
   order-theoretic data to a genuine adjunction between preorder categories.
2. A local `EPPair` is not merely a retraction. Order-theoretically it is a
   Galois insertion together with Scott continuity of both maps. Replacing it
   by a bare `GaloisInsertion` would lose continuity; retaining a thin
   domain-specific extension or proved bridge is appropriate.
3. A local kernel operator is the order-dual analogue of mathlib's
   `ClosureOperator`. The direction of the inequality is essential:
   `KernelOperator.k x ≤ x`, whereas `ClosureOperator` is inflationary.
4. Lemma 3.2.6 has a direct mathlib target:
   `ScottContinuous.fromProd`. Product pairing and product maps are also
   supported by `ScottContinuous.prodMk` and `ScottContinuous.prod`.
5. Mathlib's bundled `ωCPO` category is not the textbook category `DCPO`.
   It uses `OmegaCompletePartialOrder` and omega-continuous morphisms. The
   pinned file proves `HasLimits ωCPO`, but does not provide the arbitrary
   colimits, general directed completeness, or Scott-continuous category needed
   by Theorems 3.3.1--3.3.5.
6. The current Chapter 3 categorical interfaces are concrete, hand-written
   records (`DiagramData`, `Cone`, `Cocone`, `DCPOHasAllLimits`, and related
   predicates), not instances of mathlib's `Category`, `IsLimit`, `IsColimit`,
   `HasLimits`, `HasColimits`, `CartesianMonoidalCategory`, or
   `MonoidalClosed`. They may encode useful mathematical data, but a green
   build does not establish the mathlib-facing categorical statements.
7. In the pinned mathlib, the old `CartesianClosed` name is deprecated in
   favor of a cartesian monoidal structure together with `MonoidalClosed`.
   Future category-level work should use the current interface rather than
   introducing another parallel cartesian-closed record.

## Per-Declaration Audit

| # | Source ID | Local topic | Pinned mathlib candidate | Class | Recommended action |
|---:|---|---|---|---|---|
| 1 | `def-3-1-1` | Section-retraction pairs | `Function.LeftInverse`; `OrderHom`; Galois insertion infrastructure | `bridge` | Keep a domain-specific continuous pair, but expose its retraction law as `Function.LeftInverse` and its maps as standard homs where useful. |
| 2 | `prop-3-1-2` | Structures inherited by monotone retracts | `Function.LeftInverse.injective`, `RightInverse.surjective`; `GaloisInsertion` lifting lemmas | `partial` | Reuse generic inverse and lifted-order lemmas clause by clause; the local unpointed DCPO clause has no exact mathlib class target. |
| 3 | `lemma-3-1-3` | Retraction image of a basis | No domain-basis or way-below API found | `absent` | Keep local and downstream of the Chapter 2 basis API. |
| 4 | `thm-3-1-4` | Continuous retracts of continuous domains | Retraction and Scott-continuity infrastructure only | `absent` | Keep local; first align the Chapter 2 continuous-DCPO hierarchy and the pair structure. |
| 5 | `thm-3-1-5` | Continuous domains as retracts of algebraic domains | No continuous/algebraic DCPO or ideal-completion theorem found | `absent` | Keep local; this is a later domain-theory contribution, not an initial mathlib bridge. |
| 6 | `prop-3-1-6` | Basis ideal-completion retraction | `Order.Ideal`, `GaloisInsertion`, `ScottContinuous` infrastructure | `absent` | Retain the abstract-basis ideal construction; ordinary `Order.Ideal` does not cover the whole relation-parametric statement. |
| 7 | `prop-3-1-7` | Images of continuous idempotents | `ClosureOperator` on the order dual; subtype and fixed-point infrastructure | `partial` | Add a proved kernel/dual-closure bridge; keep the DCPO and way-below conclusions local. |
| 8 | `prop-3-1-8` | Scott topology on an idempotent image | `Topology.scott`, `Topology.IsScott`, induced/subtype topology infrastructure | `partial` | First use the Chapter 2 Scott-topology equality bridge, then express the restriction as an induced topology theorem. |
| 9 | `def-3-1-9` | Preliminary adjunction via least preimages | `GaloisConnection.isLeast_l`, `GaloisConnection.isGLB_l` | `bridge` | Keep the textbook form as a wrapper and prove equivalence to `GaloisConnection`. |
| 10 | `prop-3-1-10` | Equivalent adjunction formulations | `GaloisConnection.monotone_intro`, unit/counit, `isLeast_l`, and dual results | `direct` | Reimplement the equivalence theorem using the standard API. |
| 11 | `def-3-1-11` | Official order adjunction | `GaloisConnection`; `GaloisConnection.adjunction` | `bridge` | Make `GaloisConnection` the internal normal form; retain the textbook name as a wrapper and expose the genuine preorder-category adjunction when needed. |
| 12 | `prop-3-1-12` | Basic adjunction laws | `GaloisConnection.monotone_l`, `monotone_u`, `isLUB_l_image`, dual lemmas; `GaloisInsertion`/`GaloisCoinsertion` | `direct` | Replace duplicate proofs with standard declarations and keep numbered wrappers. |
| 13 | `prop-3-1-13` | Complete-lattice adjoint criterion | `LowerAdjoint`, `GaloisConnection.lowerAdjoint`, complete-lattice `sInf`/`sSup` API | `partial` | Bridge the local existence predicates to semibundled adjoints; retain the criterion proof where mathlib has no single matching theorem. |
| 14 | `prop-3-1-14` | Adjunctions between DCPOs | `GaloisConnection.isLUB_l_image`, root `ScottContinuous` | `partial` | Derive lower-adjoint Scott continuity from mathlib LUB preservation; way-below preservation remains local. |
| 15 | `def-3-1-15` | Embedding-projection pairs | `GaloisInsertion` plus `ScottContinuous` on both maps | `bridge` | Provide conversions in both directions under partial-order hypotheses; do not discard continuity fields. |
| 16 | `prop-3-1-16` | Embeddings reflect approximation | Galois-insertion infrastructure, but no way-below API | `absent` | Keep local; position it after the future way-below bridge/module. |
| 17 | `prop-3-1-17` | Kernel operators and their images | `ClosureOperator` through `OrderDual`; fixed-point/range and subtype tools | `partial` | Refactor elementary kernel laws through the dual closure API; retain domain-specific DCPO and approximation results. |
| 18 | `prop-3-1-18` | Algebraic images of closure operators | `ClosureOperator`, `DirSupClosed`, `IsCompactElement`, `IsCompactlyGenerated` specializations | `partial` | Separate the complete-lattice specialization from the general algebraic-DCPO theorem. |
| 19 | `def-3-2-1` | Cartesian product | Lean `Prod`; standard product order | `direct` | Keep only the source-facing abbreviation if needed. |
| 20 | `prop-3-2-2` | Product DCPO structure | `isLUB_prod`, `IsLUB.prod`; omega-CPO product instance | `partial` | Reuse coordinatewise LUB lemmas; do not use the omega-CPO instance as proof of the local general DCPO result. |
| 21 | `prop-3-2-3` | Product projections, pairing, and maps | `ScottContinuous.prodMk`, `ScottContinuous.prod` | `direct` | Replace local duplicate product-continuity proofs with thin wrappers. |
| 22 | `prop-3-2-4` | Product approximation, bases, and compactness | Product LUB API and `IsCompactElement`; no way-below/domain-basis API | `partial` | Reuse product and compact-element infrastructure, retaining way-below and basis results locally. |
| 23 | `lemma-3-2-5` | Finite products in full subcategories | `ObjectProperty.IsClosedUnderFiniteProducts`, `HasFiniteProducts`, product universal properties | `partial` | Replace custom full-subcategory records with actual category/object-property interfaces before seeking alignment; the external comparison theorem remains proof debt. |
| 24 | `lemma-3-2-6` | Separate Scott continuity | `ScottContinuous.fromProd` | `direct` | Make the numbered theorem a direct wrapper and remove the duplicated long proof. |
| 25 | `lemma-3-2-7` | Exponentials as continuous-function spaces | `MonoidalClosed`, curry/uncurry and hom-equivalence infrastructure | `partial` | First build the genuine DCPO category and cartesian monoidal structure; then state the comparison as an isomorphism of exponential objects. |
| 26 | `prop-3-2-8` | Coalesced sums are pointed DCPOs | `WithBot` and sum/order infrastructure only; no coalesced-sum CPO construction found | `absent` | Keep the quotient-like coalesced construction local and prove its universal behavior independently. |
| 27 | `prop-3-2-9` | Coalesced sums as strict coproducts | Generic coproduct API only; no strict pointed-DCPO category found | `absent` | Do not identify the current carrier-level record with `IsColimit`; build the strict category first. |
| 28 | `thm-3-3-1` | Completeness of `DCPO` | Generic `CategoryTheory.IsLimit`/`HasLimits`; `ωCPO` has limits only for omega CPOs | `partial` | Convert the concrete commuting-tuple construction into a genuine `IsLimit` for a bundled general-DCPO category. |
| 29 | `thm-3-3-2` | Cocompleteness of `DCPO` | Generic colimit infrastructure; no general DCPO theorem found | `absent` | Preserve the documented external axiom boundary until a source-backed construction is formalized in the genuine category. |
| 30 | `thm-3-3-3` | `DCPO` cartesian closed, complete, cocomplete | `HasLimits`, `HasColimits`, `CartesianMonoidalCategory`, `MonoidalClosed`; omega-CPO limits as a specialization | `partial` | Replace the custom aggregate predicate with actual instances only after items 28, 29, and the function-space adjunction are category-level. |
| 31 | `thm-3-3-4` | Strict pointed `DCPO` monoidal closed, complete, cocomplete | Generic monoidal-closed and limit APIs; no strict pointed-DCPO category found | `absent` | Keep local proof debt explicit; carrier-level smash curry/uncurry is support, not yet a `MonoidalClosed` instance. |
| 32 | `thm-3-3-5` | Pointed `DCPO` cartesian closed | Generic closed-category API; no pointed general-DCPO category found | `absent` | Build the actual category and natural hom equivalence before claiming mathlib alignment. |
| 33 | `def-3-3-6` | Expanding sequences of e-p pairs | Nat-indexed functors, `GaloisInsertion`, generic diagram infrastructure | `partial` | Represent the sequence as a functor into the future DCPO category plus coherent e-p data; keep the source wrapper. |
| 34 | `thm-3-3-7` | Bilimits of expanding sequences | Generic limits/colimits only; no domain-theoretic bilimit theorem found | `absent` | Keep local; later restate as compatible `IsLimit` and `IsColimit` data in the bundled category. |
| 35 | `lemma-3-3-8` | Colimiting-cocone criterion | `CategoryTheory.IsColimit` and extensionality infrastructure | `partial` | Translate the current elementwise criterion to `IsColimit` after the category bridge exists. |
| 36 | `prop-3-3-9` | Bilimit as a subdomain of a cocone | No matching domain-theoretic result found | `absent` | Keep local and downstream of the genuine bilimit theorem. |
| 37 | `cor-3-3-10` | Bilimit is both restricted colimit and limit | Generic `IsLimit`/`IsColimit` APIs | `partial` | Replace the custom coincidence record with a pair of genuine universal-property witnesses. |
| 38 | `thm-3-3-11` | Bilimits preserve continuity and algebraicity | No continuous/algebraic DCPO or bilimit preservation theorem found | `absent` | Keep local; this is a late contribution candidate after Chapters 2 and 3 categorical foundations stabilize. |

## Totals

| Class | Count |
|---|---:|
| `direct` | 5 |
| `bridge` | 4 |
| `partial` | 16 |
| `absent` | 13 |
| **Total** | **38** |

## Recommended Alignment Order

### Wave 1: order-theoretic standardization

1. Bridge local `Adjunction` to `GaloisConnection`.
2. Reimplement items 10 and 12 from the Galois-connection API.
3. Bridge `EPPair` to a Scott-continuous `GaloisInsertion`.
4. Express kernel operators through the order dual of `ClosureOperator`.

### Wave 2: products and separate continuity

1. Reimplement items 19, 21, and 24 from `Prod` and the pinned
   Scott-continuity product API.
2. Keep the general DCPO product proof separate from the omega-CPO instance.
3. Connect compact-product results to `IsCompactElement` after the Chapter 2
   compactness bridge exists.

### Wave 3: genuine category layer

1. Define a bundled category of local general DCPOs and Scott-continuous maps.
2. Replace `DiagramData`, `Cone`, and `Cocone` theorem interfaces with
   `Functor`, `CategoryTheory.Cone`, `CategoryTheory.Cocone`, `IsLimit`, and
   `IsColimit`.
3. Transport the existing commuting-tuple construction into `HasLimits`.
4. Formalize or source-discharge cocompleteness before defining
   `HasColimits`.
5. Build the cartesian monoidal and `MonoidalClosed` instances from the
   continuous-function-space hom equivalence.
6. Only then translate expanding-sequence bilimits and strict pointed
   constructions.

## Proof-Debt Boundary

The current Chapter 3 audit reports:

- external axioms:
  `lemma_3_2_5_full_subcategory_products_cartesian_full`,
  `lemma_3_2_7_exponential_is_function_space_full`,
  `theorem_3_3_2_dcpo_cocomplete`;
- admitted theorem:
  `theorem_3_3_4_strict_pointed_dcpo_cocomplete`.

Items depending on these declarations are not presently mathlib contribution
candidates. The two Chapter 2 admitted category-equivalence theorems are also
reported transitively by the Chapter 3 build.

## Validation

- Mapping coverage: 38 report rows, 38 unique map IDs, 0 missing, 0 extra.
- Classification arithmetic: 5 direct + 4 bridge + 16 partial + 13 absent = 38.
- `python3 skills/domain-theory-lean4-formalization/scripts/audit_chapter.py 3`:
  pass; 38 mapped items resolved; TeX review 38/38.
- `lake build Practice.DomainTheory.Chapter03.NumberedItems`: pass as part of
  the chapter audit, with the expected Chapter 3 admitted-theorem warning and
  two transitive Chapter 2 admitted-theorem warnings.
- `git diff --check -- docs/chapter3-mathlib-alignment.md`: pass.
- No Lean declaration was changed by this audit.

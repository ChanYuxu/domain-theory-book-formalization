# Chapter 2 mathlib Alignment Audit

Audit date: 2026-07-29

Scope: all 57 mapped declarations in `docs/chapter2-map.json`.

Those 57 textbook items contain 166 mapped Lean-name references (165 unique
names). Each mapped name is covered by its source item's classification below;
mixed items identify the declaration-level exception in the candidate and
action columns. Unmapped proof helpers are not silently treated as aligned.
Their public/private and module-ownership status requires a separate API-surface
audit before any mathlib submission.

Project baseline:

- Lean: `leanprover/lean4:v4.30.0-rc2`
- mathlib release: `v4.30.0-rc2`
- mathlib commit: `5450b53e5ddc75d46418fabb605edbf36bd0beb6`
- chapter build target: `Practice.DomainTheory.Chapter02`

This is an API-alignment audit, not a source audit or human approval record. A
failed name search is recorded conservatively as "no counterpart found in the
pinned mathlib", not as a claim that no such result exists mathematically.

## Classification

- `direct`: the mathlib declaration has the required semantics and can normally
  be used directly inside the source-exact textbook wrapper.
- `bridge`: the semantics agree, but a proved conversion is needed because the
  representation, bundling, or typeclass assumptions differ.
- `partial`: mathlib supplies a specialization or useful infrastructure, but
  not the whole textbook declaration.
- `absent`: no matching declaration was found in the pinned mathlib.

The classification is at the mapped textbook-item level. An item containing
several local declarations is assigned its most conservative applicable class.

## Executive Findings

1. `IsDcpo` must not be replaced by mathlib's `CompletePartialOrder`.
   The local predicate asks for suprema of nonempty directed sets and does not
   imply a least element. Mathlib's class includes `OrderBot` and a chosen
   `sSup`; it is a pointed complete partial order. This is the highest-risk name
   collision in Chapter 2.
2. The local general `ScottContinuous` and mathlib's root
   `ScottContinuous` are close enough for a bridge under the relevant order
   hypotheses. However, mathlib's bundled `ContinuousHom` is based on
   `ωScottContinuous`, so it is not a replacement for the local hom type used
   with arbitrary directed suprema.
3. The local `Compact x := WayBelow x x` has a strong target:
   mathlib's `IsCompactElement x`. The formulations use the same nonempty
   directed-LUB test, modulo the local `WayBelow` packaging.
4. The local Scott topology should be connected to
   `Topology.scott α Set.univ` and `Topology.IsScott`. The order-theoretic
   versus topological continuity result already has a mathlib theorem and should
   be a thin textbook wrapper.
5. Mathlib currently has no general Chapter 2 API for way-below, continuous
   dcpos, abstract bases, approximable relations, or the categories `CONT` and
   `ALG`. These are the strongest potential contribution areas, but they should
   be proposed as small dependency-ordered modules rather than as the whole
   chapter.
6. `Order.Ideal` is useful for ordinary orders, but the textbook's ideals of an
   abstract basis are parameterized by a relation that need not already be a
   bundled order. Reusing the name or type without a semantic bridge would hide
   assumptions.

## Per-Declaration Audit

| # | Source ID | Local topic | Pinned mathlib candidate | Class | Recommended action |
|---:|---|---|---|---|---|
| 1 | `def-2-1-1` | Preorder and partial-order relation predicates | `IsRefl`, `IsTrans`, `IsAntisymm`; bundled `Preorder`, `PartialOrder` | `bridge` | Keep relation predicates; prove small conversion lemmas to standard relation classes. |
| 2 | `prop-2-1-2` | Order dual | `OrderDual`; standard dual instances | `direct` | Implement the textbook wrapper from the existing instances. |
| 3 | `def-2-1-3` | Upper/lower sets, bounds, suprema, completeness | `IsUpperSet`, `IsLowerSet`, `upperBounds`, `lowerBounds`, `IsLUB`, `IsGLB`, `CompleteLattice` | `partial` | Alias the elementary predicates where statements coincide; keep the existence-only completeness predicate distinct from a chosen `CompleteLattice`. |
| 4 | `prop-2-1-4` | Elementary LUB/GLB laws | `IsLUB.mono`, `isLUB_congr`, `IsLUB.upperBounds_eq`, and dual lemmas | `direct` | Reprove wrappers with the standard LUB/GLB API and remove duplicate internal arguments. |
| 5 | `prop-2-1-5` | Closure systems form complete orders | `ClosureOperator`, `ClosureOperator.ofCompletePred`, `ClosureOperator.gi`, `GaloisInsertion` | `partial` | Add a bridge from the local closure-system predicate; do not replace the source-facing statement. |
| 6 | `def-2-1-6` | Monotone maps | `Monotone`, `OrderHom` | `bridge` | Make `Monotone` the internal normal form and retain the textbook name as a reducible wrapper or theorem. |
| 7 | `prop-2-1-7` | Fixed points of a monotone endomap | `OrderHom.lfp`, `OrderHom.gfp`, `OrderHom.isLeast_lfp`, `fixedPoints.completeLattice` | `direct` | Use mathlib's fixed-point lattice API inside the wrapper. |
| 8 | `def-2-1-8` | Directed sets, chains, ideals, filters | `DirectedOn`, `IsChain`, `Order.IsIdeal`, `Order.Ideal` | `bridge` | Bridge `DirectedSet A` to `A.Nonempty ∧ DirectedOn (· ≤ ·) A`; keep relation-level textbook notions where more general. |
| 9 | `prop-2-1-9` | Finite nonempty joins in a directed set | `Finset.sup'`, `SupClosed.finsetSup'_mem`, directed finite-sup lemmas | `partial` | Reuse finite-set infrastructure; retain the weaker-hypothesis local theorem. |
| 10 | `def-2-1-10` | Monotone nets and subnets | `OrderHom` and `Directed` infrastructure only | `partial` | Keep the local API; align index-order assumptions and map fields with standard structures where possible. |
| 11 | `lemma-2-1-11` | Finite-principal-lattice subnet | No exact counterpart found | `absent` | Keep local; document the finite-subset construction and test it independently. |
| 12 | `prop-2-1-12` | Iterated directed suprema | `IsLUB` and indexed/union LUB lemmas | `partial` | Refactor the proof around standard `IsLUB` composition lemmas, without strengthening the source statement. |
| 13 | `def-2-1-13` | DCPO | `CompletePartialOrder`; `ConditionallyCompletePartialOrderSup` | `absent` | Preserve `IsDcpo`/`IsDcpoOrder`; explicitly document that mathlib's `CompletePartialOrder` is pointed and therefore stronger. |
| 14 | `prop-2-1-15` | DCPO iff chain suprema exist | No exact counterpart found; omega-CPO APIs are only special cases | `absent` | Keep the Markowsky dependency isolated and source-audited; do not discharge it by a CPO typeclass conversion. |
| 15 | `prop-2-1-16` | Pointed DCPO iff every monotone endomap has a least fixed point | Fixed-point and CPO infrastructure, but no matching equivalence found | `partial` | Keep the external theorem boundary explicit; reuse only the fixed-point-order API after the theorem is available. |
| 16 | `def-2-1-17` | Scott-continuous, strict, constant, and bundled maps | `ScottContinuous`, `ωScottContinuous`, `ContinuousHom` | `partial` | Prove a general Scott-continuity bridge; do not identify local `ScottContFun` with omega-only `ContinuousHom`. |
| 17 | `prop-2-1-18` | Function spaces of Scott-continuous maps | Omega analogue via `ContinuousHom` and omega-CPO instances | `partial` | Use the omega implementation as a design reference; retain the general directed-sup theorem locally. |
| 18 | `thm-2-1-19` | Kleene fixed-point theorem | `iterateChain`, `ωSup_iterate_mem_fixedPoint`, `ωSup_iterate_le_prefixedPoint`, `OrderHom.lfp_eq_sSup_iterate` | `partial` | Reuse the omega-chain lemmas after proving the local omega-CPO bridge; keep the stronger surrounding theorem separate. |
| 19 | `lemma-2-1-20` | Fixed-point induction | `OrderHom.lfp_induction` | `partial` | Use the complete-lattice result only for that specialization; keep the admissible-subset/DCPO theorem. |
| 20 | `lemma-2-1-21` | Fixed-point invariance | No exact counterpart found | `absent` | Keep as a local theorem; express commuting hypotheses with standard function/order-hom notation where possible. |
| 21 | `def-2-2-1` | Way-below and compact elements | `IsCompactElement` for compactness; no general way-below relation found | `partial` | Add and prove `Compact x ↔ IsCompactElement x`; keep `WayBelow` local. |
| 22 | `prop-2-2-2` | Basic way-below laws | No way-below API found | `absent` | Keep local; this is a candidate foundation for a future mathlib contribution. |
| 23 | `def-2-2-3` | Bases and approximants | No domain-basis API found | `absent` | Keep local and stabilize names only after the way-below layer is settled. |
| 24 | `prop-2-2-4` | Elementary basis facts | No exact counterpart found | `absent` | Keep local; derive all facts from one canonical basis predicate to reduce duplicated assumptions. |
| 25 | `cor-2-2-5` | Smallest basis and compact elements | `IsCompactElement` covers the compactness component | `partial` | Bridge compactness first, then keep the smallest-basis conclusion local. |
| 26 | `def-2-2-6` | Continuous, algebraic, and omega domains | `IsCompactlyGenerated` only for complete lattices | `absent` | Do not equate algebraic DCPOs with `IsCompactlyGenerated`; consider a new general DCPO hierarchy. |
| 27 | `prop-2-2-7` | Characterizations of continuous/algebraic domains | No exact counterpart found | `absent` | Keep local; split reusable characterization lemmas from textbook packaging. |
| 28 | `def-2-2-8` | Inductive closure systems | `ClosureOperator`, `DirSupClosed`, `SupClosed` | `partial` | Represent the closure and directed-sup conditions using existing predicates when assumptions match. |
| 29 | `prop-2-2-9` | Inductive closure systems are algebraic | Closure-operator and compact-generation infrastructure | `partial` | Reuse infrastructure but retain the domain-theoretic theorem and its exact hypotheses. |
| 30 | `prop-2-2-10` | Recovering order from basis approximants | No exact counterpart found | `absent` | Keep local; likely belongs with a future basis API rather than a standalone contribution. |
| 31 | `prop-2-2-11` | Basis criterion for Scott continuity | `ScottContinuous` and `IsLUB` infrastructure | `partial` | State the bridge to mathlib Scott continuity, then prove the basis criterion locally. |
| 32 | `prop-2-2-12` | Fixed-point chains from an omega basis | Omega-CPO/Kleene infrastructure, but no basis-chain theorem found | `partial` | Keep the external dependency isolated; do not replace it with a generic omega-CPO theorem. |
| 33 | `prop-2-2-13` | Countable basis gives a cofinal omega chain | `OmegaCompletePartialOrder.Chain` infrastructure | `partial` | Keep the cofinal-chain construction local and feed its result into the omega-CPO bridge. |
| 34 | `prop-2-2-14` | Omega-ccpos, omega continuity, and DCPO recovery | `OmegaCompletePartialOrder`, `ωScottContinuous` | `partial` | Prove representation bridges; the continuous-domain-to-DCPO result remains local because it uses basis data. |
| 35 | `lemma-2-2-15` | Interpolation of way-below | No way-below API found | `absent` | Keep local; mark as a central prospective contribution after the base relation is accepted. |
| 36 | `cor-2-2-16` | Way-below versus directed suprema | No way-below API found | `absent` | Keep local and derive from the interpolation layer. |
| 37 | `prop-2-2-17` | Principal ideals and locality | `Set.Iic`, subtype orders, `Order.Ideal.principal` | `partial` | Distinguish the `Iic` subtype from an `Order.Ideal` object and bridge only under matching order assumptions. |
| 38 | `prop-2-2-18` | Compact elements and finite joins | `IsCompactElement`; `CompleteLattice.isCompactElement_finsetSup` | `partial` | Reuse the complete-lattice specialization, but retain the weaker local finite-join theorem. |
| 39 | `cor-2-2-19` | Algebraic complete lattices | `IsCompactlyGenerated` and compact-generation lemmas | `bridge` | Prove equivalence for complete lattices; use mathlib's predicate as the internal normal form in this specialization. |
| 40 | `def-2-2-20` | Abstract bases | No exact counterpart found | `absent` | Keep local; design this API before ideal completion and approximable relations. |
| 41 | `def-2-2-21` | Ideals and ideal completion of an abstract basis | `Order.IsIdeal`, `Order.Ideal` | `partial` | Reuse only after a proved relation/order bridge; do not assume the abstract-basis relation is already a bundled preorder. |
| 42 | `prop-2-2-22` | Properties of ideal completion | `Order.Ideal` lattice API under stronger order assumptions | `partial` | Factor out the ordinary-order specialization; retain the relation-parametric theorem. |
| 43 | `prop-2-2-23` | Products of abstract bases and ideal completions | No exact counterpart found | `absent` | Keep local; base it on the stabilized abstract-basis and ideal-completion APIs. |
| 44 | `prop-2-2-24` | Universal property of extension from a basis | `ScottContinuous`, `OrderHom`, and generic universal-property infrastructure | `partial` | Keep the theorem; use standard hom structures in the implementation without weakening the universal property. |
| 45 | `prop-2-2-25` | Continuous domains as ideal completions | No exact counterpart found | `absent` | Keep local; treat as a culmination theorem, not an initial mathlib contribution. |
| 46 | `cor-2-2-26` | Continuous maps determined by basis values | No domain-basis API found | `absent` | Keep local and derive from the extension theorem. |
| 47 | `def-2-2-27` | Approximable relations | No exact counterpart found | `absent` | Keep local; candidate only after abstract bases and ideal completion stabilize. |
| 48 | `thm-2-2-28` | Abstract bases and approximable maps equivalent to `CONT` | Generic `CategoryTheory.Equivalence` only | `absent` | Keep the current proof debt explicit; no mathlib theorem can discharge the domain-specific equivalence. |
| 49 | `thm-2-2-29` | Preorders and approximable maps equivalent to `ALG` | Generic category-theory infrastructure only | `absent` | Keep the current proof debt explicit; first construct and verify both categories and functors. |
| 50 | `def-2-3-1` | Scott topology | `DirSupClosed`, `DirSupInacc`, `Topology.scott`, `Topology.IsScott`, `WithScott` | `bridge` | Prove the local topology equals `Topology.scott α Set.univ`; then use the standard topology internally. |
| 51 | `prop-2-3-2` | Order and separation properties | `Topology.IsScott.instT0Space`, specialization-order and closed-interval tools | `partial` | Reuse the T0 result; retain and separately prove the Hausdorff/trivial-order characterization. |
| 52 | `prop-2-3-3` | Directed suprema characterized by Scott neighborhoods | `DirSupInacc` and Scott-open characterizations | `partial` | Recast the proof through the standard Scott-open API; keep the textbook neighborhood wrapper. |
| 53 | `prop-2-3-4` | Order-theoretic versus topological Scott continuity | `Topology.IsScott.scottContinuousOn_iff_continuous` | `direct` | Make this a thin wrapper after the local Scott-topology equality bridge. |
| 54 | `prop-2-3-5` | Way-below as Scott interior | Scott-topology and interior APIs; no way-below API | `partial` | Keep local and use the standard topology side through the bridge. |
| 55 | `prop-2-3-6` | Scott opens generated by way-below supports | Scott-open infrastructure; no basis/way-below API | `partial` | Keep local; expose reusable support-set lemmas for a future domain-basis module. |
| 56 | `prop-2-3-7` | Scott opens of ideal completions | `Order.Ideal` and Scott-topology infrastructure | `partial` | Keep local; bridge each layer independently before composing the theorem. |
| 57 | `lemma-2-3-8` | Scott opens as unions of filters | Ideal/filter and Scott-open infrastructure | `partial` | Keep local; avoid changing the theorem into a stronger lattice-specific variant merely to reuse an API. |

## Totals

| Class | Count |
|---|---:|
| `direct` | 4 |
| `bridge` | 5 |
| `partial` | 29 |
| `absent` | 19 |
| **Total** | **57** |

## Recommended Alignment Order

### Wave 1: low-risk standardization

1. Add bridge lemmas for relation classes, monotonicity, directed sets, LUB/GLB,
   and compact elements.
2. Reimplement the direct wrappers for items 2, 4, 7, and 53 using mathlib.
3. Add tests proving both directions of each non-definitional bridge.

### Wave 2: topology and complete-lattice specializations

1. Prove the local Scott topology equals `Topology.scott α Set.univ`.
2. Align the complete-lattice specialization of algebraicity with
   `IsCompactlyGenerated`.
3. Reuse `ClosureOperator` and fixed-point APIs where their assumptions match
   the textbook statements exactly.

### Wave 3: domain-theory contribution candidates

1. General way-below and its elementary laws.
2. Continuous and algebraic DCPO predicates, explicitly distinct from pointed
   `CompletePartialOrder`.
3. Basis and interpolation results.
4. Abstract bases, ideal completion, and approximable relations.

The category equivalences should remain downstream applications until the
underlying objects, morphisms, and universal properties have proof-complete,
stable APIs.

## Proof-Debt Boundary

The current chapter audit reports:

- external axioms:
  `markowsky_dcpo_of_chain_sups`,
  `prop_2_1_16_pointed_dcpo_iff_lfp`,
  `prop_2_2_12_omega_basis_fixpoint_chain_full`;
- admitted textbook theorems:
  `theorem_2_2_28_abstract_bases_equiv_CONT`,
  `theorem_2_2_29_preorders_equiv_ALG`.

No item depending on those declarations is presently a mathlib contribution
candidate. A successful `lake build` establishes elaboration only; it does not
remove this proof debt.

## Validation

- Mapping coverage: 57 report rows, 57 unique map IDs, 0 missing, 0 extra.
- Classification arithmetic: 4 direct + 5 bridge + 29 partial + 19 absent = 57.
- `python3 skills/domain-theory-lean4-formalization/scripts/audit_chapter.py 2`:
  pass; 57 mapped items resolved; TeX review 57/57; two expected warnings from
  the admitted theorems.
- `lake build Practice.DomainTheory.Chapter02`: pass as part of the chapter
  audit.
- `git diff --check -- docs/chapter2-mathlib-alignment.md`: pass.

No Lean declaration was changed by this audit.

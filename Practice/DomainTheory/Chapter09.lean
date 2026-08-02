import Practice.DomainTheory.Chapter08

set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-!
# Abramsky--Jung, Domain Theory, Chapter 9

The final chapter is a guide to the literature.  This file turns the guide into
structured bibliography metadata that can be extended without changing earlier
formalizations.
-/

namespace AbramskyJung
namespace Chapter9

/-- A bibliographic citation key and a short description of its role. -/
structure Citation where
  key : String
  topic : String

/-- A reading-guide entry grouped by chapter theme. -/
structure LiteratureEntry where
  guideSection : String
  citations : List Citation
  note : String

/-- The Scott 1969 citation entry used in the foundations part of the guide. -/
def scott1969 : Citation :=
  { key := "Sco69", topic := "Scott domains and fixed points" }

def foundationsEntry : LiteratureEntry :=
  { guideSection := "Foundations and overview",
    citations :=
      [ scott1969,
        { key := "Sco70", topic := "continuous lattices" },
        { key := "LNS82", topic := "history of fixed point theorems" } ],
    note := "Early sources for the order-theoretic fixed point method." }

def categoryEntry : LiteratureEntry :=
  { guideSection := "Categories of domains",
    citations :=
      [ { key := "Jun89", topic := "cartesian closed categories" },
        { key := "Jun90", topic := "classification results" } ],
    note := "Background for the hierarchy in Chapter 4." }

def recursiveEquationEntry : LiteratureEntry :=
  { guideSection := "Recursive domain equations",
    citations :=
      [ { key := "Fre91", topic := "algebraically compact categories" },
        { key := "Fre92", topic := "minimal invariance" },
        { key := "Pit93b", topic := "proof principles for solutions" } ],
    note := "Canonicity and proof principles for recursive solutions." }

def logicEntry : LiteratureEntry :=
  { guideSection := "Logic and duality",
    citations :=
      [ { key := "Abr91b", topic := "domain theory in logical form" },
        { key := "Joh82", topic := "Stone duality and pointfree topology" } ],
    note := "The logical viewpoint developed in Chapter 7." }

/-- The main chapter-to-topic map of the guide to the literature. -/
def literatureGuide : List LiteratureEntry :=
  [foundationsEntry, categoryEntry, recursiveEquationEntry, logicEntry]

/-- A guide contains a citation key exactly when some entry lists it. -/
def ContainsCitation (guide : List LiteratureEntry) (key : String) : Prop :=
  ∃ entry ∈ guide, ∃ c ∈ entry.citations, c.key = key

theorem contains_scott_1969 : ContainsCitation literatureGuide "Sco69" := by
  unfold ContainsCitation literatureGuide
  refine ⟨foundationsEntry, by simp, ?_⟩
  refine ⟨scott1969, by simp [foundationsEntry], rfl⟩

end Chapter9
end AbramskyJung

import Practice.DomainTheory.Chapter08

set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-!
# Abramsky--Jung, Domain Theory, Chapter 9

The final chapter is a one-page guide to the literature.  It contains no
mathematical theorem/proof items.  This file translates the complete guide into
queryable bibliography data: systematic accounts, reading by book section,
programming-language textbooks, applications, and related Handbook chapters.
-/

namespace AbramskyJung
namespace Chapter9

/-- A bibliography key together with the role assigned to it on source page
152. -/
structure Citation where
  key : String
  topic : String
deriving DecidableEq, Repr

/-- One entry in the source's reading guide. -/
structure LiteratureEntry where
  guideSection : String
  citations : List Citation
  note : String
deriving DecidableEq, Repr

/-- The six systematic or introductory accounts listed at the start of
Chapter 9. -/
def overviewEntry : LiteratureEntry :=
  { guideSection := "Systematic accounts and introductions"
    citations :=
      [ { key := "Sco81", topic := "Scott's systematic lecture notes" },
        { key := "Plo81", topic := "Plotkin's systematic lecture notes" },
        { key := "GS90", topic := "introductory exposition by Gunter and Scott" },
        { key := "GHK+80", topic := "continuous lattices" },
        { key := "Joh82", topic := "Stone duality and continuous lattices" },
        { key := "DP90", topic := "introduction to partial orders" } ]
    note := "General sources recommended before the section-by-section list." }

def section2Entry : LiteratureEntry :=
  { guideSection := "Section 2"
    citations :=
      [ { key := "DP90", topic := "partial orders" },
        { key := "Joh82", topic := "Stone duality and continuous lattices" } ]
    note := "Further reading for Section 2." }

def section3Entry : LiteratureEntry :=
  { guideSection := "Section 3"
    citations :=
      [ { key := "Plo81", topic := "domain-theoretic constructions" },
        { key := "Gun92b", topic := "semantics and domains" },
        { key := "Win93", topic := "formal semantics" } ]
    note := "Further reading for Section 3." }

def section4Entry : LiteratureEntry :=
  { guideSection := "Section 4"
    citations :=
      [ { key := "Jun89", topic := "cartesian closed categories of domains" },
        { key := "Jun90", topic := "classification of domain categories" } ]
    note := "Further reading for Section 4." }

def section5Entry : LiteratureEntry :=
  { guideSection := "Section 5"
    citations :=
      [ { key := "SP82", topic := "recursive domain equations" },
        { key := "Fre91", topic := "algebraically compact categories" },
        { key := "Fre92", topic := "algebraic compactness" },
        { key := "Pit93b", topic := "recursive types and proof principles" },
        { key := "Pit93a", topic := "recursive types" } ]
    note := "Further reading for Section 5." }

def section6Entry : LiteratureEntry :=
  { guideSection := "Section 6"
    citations :=
      [ { key := "Plo76", topic := "powerdomains" },
        { key := "Smy78", topic := "powerdomains" },
        { key := "Win83", topic := "powerdomains and semantics" },
        { key := "Hec91", topic := "powerdomain constructions" },
        { key := "Sch93", topic := "powerdomains" } ]
    note := "Further reading for Section 6." }

def section7Entry : LiteratureEntry :=
  { guideSection := "Section 7"
    citations :=
      [ { key := "Abr90c", topic := "domain logic" },
        { key := "Abr91a", topic := "domain theory in logical form" },
        { key := "AO93", topic := "logic and domains" },
        { key := "Ong93", topic := "domain logic" },
        { key := "Hen93", topic := "logical semantics" },
        { key := "Bou94", topic := "domain logic" },
        { key := "Jen92", topic := "domain logic" },
        { key := "Jen91", topic := "domain logic" },
        { key := "Smy83b", topic := "topology and logic" } ]
    note := "Further reading for Section 7." }

/-- The complete general and section-by-section guide in source order. -/
def literatureGuide : List LiteratureEntry :=
  [ overviewEntry, section2Entry, section3Entry, section4Entry,
    section5Entry, section6Entry, section7Entry ]

/-- Textbooks on programming-language semantics listed under "Applications of
Domain Theory". -/
def programmingLanguageTextbooks : LiteratureEntry :=
  { guideSection := "Programming-language semantics textbooks"
    citations :=
      [ { key := "Sch86", topic := "denotational semantics" },
        { key := "Ten91", topic := "programming-language semantics" },
        { key := "Gun92b", topic := "semantics of programming languages" },
        { key := "Win93", topic := "formal semantics" } ]
    note := "Useful textbooks employing substantial domain theory." }

/-- One non-textbook application area listed by the source. -/
structure ApplicationArea where
  name : String
  citations : List Citation
deriving DecidableEq, Repr

/-- All six additional application areas, in source order. -/
def applicationGuide : List ApplicationArea :=
  [ { name := "Abstract interpretation and static program analysis"
      citations :=
        [ { key := "Abr90a", topic := "abstract interpretation" },
          { key := "BHA86", topic := "static program analysis" },
          { key := "AJ91", topic := "abstract interpretation" } ] },
    { name := "Databases"
      citations :=
        [ { key := "BDW88", topic := "database semantics" },
          { key := "BJO91", topic := "database domains" } ] },
    { name := "Computational linguistics"
      citations :=
        [ { key := "PS84", topic := "computational linguistics" },
          { key := "PM90", topic := "computational linguistics" } ] },
    { name := "Artificial intelligence"
      citations := [{ key := "RZ94", topic := "artificial intelligence" }] },
    { name := "Fractal image generation"
      citations := [{ key := "Eda93b", topic := "fractal image generation" }] },
    { name := "Foundations of analysis"
      citations := [{ key := "Eda93a", topic := "foundations of analysis" }] } ]

/-- Handbook chapters said to make substantial use of domain-theoretic ideas. -/
inductive HandbookChapter where
  | topology
  | algebraicSemantics
  | semanticsOfTypes
  | operationalDenotationalCorrespondence
  | abstractInterpretation
  | effectiveStructures
deriving DecidableEq, Repr

def handbookChapters : List HandbookChapter :=
  [ .topology,
    .algebraicSemantics,
    .semanticsOfTypes,
    .operationalDenotationalCorrespondence,
    .abstractInterpretation,
    .effectiveStructures ]

/-- A list of reading-guide entries contains a citation key exactly when some
entry lists a citation with that key. -/
def ContainsCitation (guide : List LiteratureEntry) (key : String) : Prop :=
  ∃ entry ∈ guide, ∃ citation ∈ entry.citations, citation.key = key

/-- Scott's 1981 lecture notes occur in the complete literature guide. -/
theorem contains_scott_1981 : ContainsCitation literatureGuide "Sco81" := by
  refine ⟨overviewEntry, by simp [literatureGuide], ?_⟩
  exact ⟨{ key := "Sco81", topic := "Scott's systematic lecture notes" },
    by simp [overviewEntry], rfl⟩

/-- Section 5's guide contains Freyd's 1991 algebraic-compactness reference. -/
theorem section5_contains_freyd_1991 :
    ContainsCitation [section5Entry] "Fre91" := by
  refine ⟨section5Entry, by simp, ?_⟩
  exact ⟨{ key := "Fre91", topic := "algebraically compact categories" },
    by simp [section5Entry], rfl⟩

end Chapter9
end AbramskyJung

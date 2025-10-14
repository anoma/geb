import GebLean.Utilities
import GebLean.Semicategory
import GebLean.FiniteQuiver
import GebLean.CategoryJudgments
import GebLean.DepCategoryJudgments
import GebLean.AcyclicQuiver
import GebLean.AcyclicCat
import GebLean.CategoryPresentation

/-!
# GebLean

The library entry point. Importing `GebLean` re-exports the core modules
that make up the project:

- `Utilities`: helper constructions that reduce boilerplate when working
  with equivalences and bundled categories.
- `Semicategory`: the semicategory structures and semifunctors.
- `FiniteQuiver`: witnesses that quivers are finite and the induced full
  subcategory of `Quiv`.
- `CategoryJudgments` and `DepCategoryJudgments`: the two encodings of the
  categorical axioms.
- `AcyclicQuiver` and `AcyclicCat`: finite acyclic quivers and the
  associated categories.
- `CategoryPresentation`: presentation of categories by generators and
  relations.
-/

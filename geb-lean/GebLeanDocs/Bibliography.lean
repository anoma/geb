import VersoManual

open Verso.Genre.Manual

/-! # Bibliography

The six published works the manual cites, as Verso bibliography
entries. Part I chapter 6 cites all six; Leivant III is additionally
cited throughout.
-/

/-- Leivant III, the manual's primary source. -/
def leivant3 : Article := {
  title := inlines!"Ramified recurrence and computational complexity \
    III: Higher type recurrence and elementary complexity",
  authors := #[inlines!"D. Leivant"],
  journal := inlines!"Annals of Pure and Applied Logic",
  year := 1999,
  month := some inlines!"March",
  volume := inlines!"96",
  number := inlines!"1-3",
  pages := some (209, 229),
  url := some "https://doi.org/10.1016/S0168-0072(98)00040-2"
}

/-- Leivant I, on word recurrence and polynomial time. -/
def leivant1 : InProceedings := {
  title := inlines!"Ramified recurrence and computational complexity I: \
    Word recurrence and poly-time",
  authors := #[inlines!"D. Leivant"],
  year := 1995,
  booktitle := inlines!"Feasible Mathematics II",
  url := some "https://doi.org/10.1007/978-1-4612-2566-9_11"
}

/-- Bellantoni and Cook's recursion-theoretic characterization of polytime. -/
def bellantoniCook : Article := {
  title := inlines!"A new recursion-theoretic characterization of the \
    polytime functions",
  authors := #[inlines!"S. Bellantoni", inlines!"S. Cook"],
  journal := inlines!"Computational Complexity",
  year := 1992,
  month := some inlines!"June",
  volume := inlines!"2",
  number := inlines!"2",
  pages := some (97, 110),
  url := some "https://doi.org/10.1007/BF01201998"
}

/-- Clote's survey of computation models and function algebras. -/
def clote : InProceedings := {
  title := inlines!"Computation models and function algebras",
  authors := #[inlines!"P. Clote"],
  year := 1999,
  booktitle := inlines!"Handbook of Computability Theory",
  series := some inlines!"Studies in Logic and the Foundations of Mathematics",
  url := some "https://doi.org/10.1016/S0049-237X(99)80033-0"
}

/-- Ritchie's classes of predictably computable functions. -/
def ritchie : Article := {
  title := inlines!"Classes of predictably computable functions",
  authors := #[inlines!"R. W. Ritchie"],
  journal := inlines!"Transactions of the American Mathematical Society",
  year := 1963,
  month := none,
  volume := inlines!"106",
  number := inlines!"1",
  pages := some (139, 173),
  url := some "https://doi.org/10.1090/S0002-9947-1963-0158822-2"
}

/-- Dal Lago, Martini and Zorzi on the soundness of general ramified recurrence. -/
def dalLagoMartiniZorzi : InProceedings := {
  title := inlines!"General Ramified Recurrence is Sound for Polynomial Time",
  authors := #[inlines!"U. Dal Lago", inlines!"S. Martini", inlines!"M. Zorzi"],
  year := 2010,
  booktitle := inlines!"Proceedings DICE 2010 (EPTCS 23)",
  url := some "https://doi.org/10.4204/EPTCS.23.4"
}

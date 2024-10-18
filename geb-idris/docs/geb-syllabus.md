# Geb Reading Group Syllabus

## Purpose

This document is intended to summarize the background, especially in category theory and polynomial functors, required to understand how Geb works.  It will serve as a guide to topics for the weekly reading group, and for attendees on how to prepare.

Practically none of the following is required just to write code in Geb!  But it is required to understand how the language works under the hood, and that would also enable a programmer to use more of it.

## Learning outline

The two main threads of theory underlying Geb are category theory and polynomial functors.  To some degree I am treating the former as the theory of (programming) languages and the latter as the theory of data structures, but in Geb they are intertwined, defined through mutual recursion:  category theory defined by data structures, data structures given semantics by category theory, and "(programming) language" emerging as a notion of its own (broader than "category").

### The big picture

The end goal of the language definition of Geb -- the point at which the language itself is finished and all else is libraries -- is what I have been calling "programming languages à la carte".  That is a reference, to "Data Types à la Carte", so the founding paper there (see the Bibliography) is one place you might start.  It illustrates how to define data structures in ways which allow for more combinators than traditional explicitly-recursive ADTs.  Geb aims to extend this notion to programming languages -- defining them in terms of individual language features and combinators on languages themselves.

### Track: category theory

Fortunately, but not just coincidentally, the aspects of category theory underpinning Geb are mainly the foundational ones -- the first few that are typically presented in books on category theory.  One of my aims in the reading group will be to communicate these foundations in terms that will be most familiar to programmers -- each of them has a clear analogue in and application to programming.

Here is a rough order of topics I'd recommend.

### Track: polynomial functors

## Bibliography

### Category theory

- [The Dao of Functional Programming by Bartosz Milewski](https://github.com/BartoszMilewski/Publications/blob/master/TheDaoOfFP/DaoFP.pdf)
- [The Joy of Abstraction by Eugenia Cheng](https://topos.site/events/joa-bookclub/)
- [Category Theory in Context by Emily Riehl](https://math.jhu.edu/~eriehl/context.pdf)
- [Paranatural Category Theory](https://arxiv.org/abs/2307.09289)
- [Paranatural Category Theory Slides](https://jacobneu.github.io/research/slides/Octoberfest-2023.pdf)
- [Paranatural Category Theory Video 1 ("(Co)ends and (co)structure")](https://www.youtube.com/watch?v=X4v5HnnF2-o)
- [Paranatural Category Theory Video 2](https://www.youtube.com/watch?v=zbWvfYqye9c)
- [A Categorical Semantics for Inductive-Inductive Definitions](https://github.com/Mzk-Levi/texts/blob/master/A%20categorical%20semantics%20for%20inductive-inductive%20definitions.pdf)
- [Coend Calculus](https://arxiv.org/abs/1501.02503)
- [Generic Programming With Adjunctions](https://www.cs.ox.ac.uk/ralf.hinze/LN.pdf)
- [Adjoint Folds](http://www.cs.ox.ac.uk/ralf.hinze/SSGIP10/AdjointFolds.pdf)
- [Conjugate Hylomorphisms](http://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/conjugate-hylos.pdf)
- [Kan Extensions for Program Optimization](https://www.cs.ox.ac.uk/ralf.hinze/Kan.pdf)
- [Data Types à la Carte](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/data-types-a-la-carte/14416CB20C4637164EA9F77097909409)
- [Richard Southwell: Category Theory for Beginners (videos)](https://www.youtube.com/playlist?list=PLCTMeyjMKRkoS699U0OJ3ymr3r01sI08l)
- [Bartosz Milewski video playlists](https://www.youtube.com/@DrBartosz/playlists)
- [Recursion schemes without the barbed wire (part 1)](https://www.youtube.com/watch?v=0y0EuoToTco)
- [Recursion schemes without the barbed wire (part 2)](https://www.youtube.com/watch?v=i-H_MqhRQNU)

### Polynomial functors

- [Polynomial Functors: A Mathematical Theory of Interaction](https://topos.site/events/poly-course/)
- [Dirichlet Functors are Contravariant Polynomial Functors](https://arxiv.org/pdf/2004.04183)
- [From Algebras and Coalgebras to (Polynomial) Dialgebras](http://cs.ru.nl/~erikpoll/publications/dialgebra.pdf)

Research note: interaction nets, polynomial GSOS, and fair merge
================================================================

Investigated against this checkout on 2026-09-18. The accompanying
[Lean prototype](InteractionExecution.lean) imports the existing implementation.

**The current polynomial GSOS implementation is already general enough to
represent the transition systems of interaction combinators and their
`amb` extension. It can also host a fair merger when its interface exposes
nonblocking progress, or when admissible executions explicitly carry a fairness
condition. Fairness does not follow merely from having GSOS, a cofree comonad,
or a universal semantics map.**

These are statements about the scope of the framework. A complete verified
encoding of interaction-net graphs is not already present in the prototype.
In particular, representing their transition system is weaker than proving a
translation preserves graph composition, distributed execution, complexity,
or a particular observational equivalence.

| Construction | Ordinary interaction combinators | Nets with `amb` | Fair merge |
| --- | --- | --- | --- |
| Existing `PolyGSOSRule` and generated distributive law | Yes, via configurations and elementary steps | Yes, using explicit branching; carry over the intended progress convention | Yes with suitable polling/scheduler behavior; arbitrary branching alone supplies no fairness guarantee |
| Existing lambda-bialgebra `universalSemantics` | Supplies the semantics of that chosen law | A single semantic value can be a branching behavior | Preserves the structure chosen for the law; does not manufacture fairness |
| Libkind–Spivak module action | Can run finite experiments on a machine encoded as matter | Can expose choices through the interaction interface | Requires fairness in the matter, interface, or specification; the action alone adds none |

The first two rows are stages of the same available construction, rather than
competing models. The third uses a different kind of interaction law.

**What the existing definitions establish.** In
[Utilities/GSOSRule.lean](../../GebLean/Utilities/GSOSRule.lean), `GSOSRule`
accepts general endofunctors on a category, chosen products, and a monad.
Its rule has the mathematical type

\[
\rho_X:\Sigma(X\times B X)\longrightarrow B(TX).
\]

The implemented conversion to a distributive law is the polynomial construction
in [PolyGSOS.lean](../../GebLean/PolyGSOS.lean): `PolyGSOSRule P Q` represents

\[
P(\mathrm{Id}\times Q)\longrightarrow Q T_P,
\]

and `polyGSOSDistributiveLaw` proves the four coherence laws for

\[
\lambda:T_P D_Q\longrightarrow D_Q T_P.
\]

Here `T_P` is the free monad and `D_Q` the cofree comonad.
Neither `PolyGSOSRule` nor this construction requires
`PolyEndoFinitary`. The finitary property is a separate definition in
[PolyAlg.lean](../../GebLean/PolyAlg.lean). Thus the implementation is not
limited to fixed finite branching.

[Utilities/LambdaBialgebra.lean](../../GebLean/Utilities/LambdaBialgebra.lean)
constructs initial and final bialgebras for a supplied distributive law, and
`universalSemantics` is their unique connecting morphism. In the polynomial
case its underlying carriers are \(T_P0\) and \(D_Q1\), the latter corresponding
to the final \(Q\)-coalgebra. The relevant existing bridges are
`polyFreeMInitialEvalEquiv` and `polyCofreeTerminalEvalEquiv`.

“Universal” here refers to these categorical properties for the selected law.
It does not assert that every particular instantiation is computationally
universal, nor does uniqueness of the map assert deterministic execution.
A nondeterministic computation may have one well-defined tree of possible
behaviors. This agrees with the role of universal semantics in
[Turi and Plotkin, especially Sections 4 and 7](https://homepages.inf.ed.ac.uk/gdp/publications/Math_Op_Sem.pdf).

**A concrete embedding, checked against the real API.** The following argument
is my construction; its GSOS law and connection to `universalSemantics` are
implemented in the prototype.

Suppose an elementary machine has states \(S\) and polynomial behavior

\[
QX=\sum_{o:O}X^{E(o)},\qquad
c:S\longrightarrow\sum_{o:O}(E(o)\longrightarrow S).
\]

Take the syntax polynomial \(P_S X=S\): one nullary operation \([s]\) per
complete state. Its free monad is \(T_{P_S}X\cong X+S\). Let
\(\iota_X:S\to T_{P_S}X\) insert a state as a constant term. Then

\[
\rho_X=Q(\iota_X)\circ c:
P_S(X\times QX)=S\longrightarrow Q(T_{P_S}X)
\]

is natural: it never inspects the variable type \(X\).
It is a morphism of polynomials, including with the repository's actual
representation of those morphisms.

The prototype's `machineGSOS` implements this construction;
`machineLaw` invokes `polyGSOSDistributiveLaw`; and
`machineSemantics` invokes `universalSemantics`.
Since \(T_{P_S}0\cong S\), mathematically the resulting semantics is the
coalgebraic unfolding of the machine. The prototype does not separately
formalize this carrier isomorphism and unfolding-identification theorem.

This construction is deliberately an embedding of complete configurations.
Its nullary signature can have infinitely many operations even when the
source language has a finite signature. It proves that the current framework
can accommodate the machine; it does not yet provide a useful algebra of
graph constructors.

For a finite net, number its cells and ports and enumerate the applicable
elementary rewrites. Use canonical fresh names so irrelevant renamings do not
create infinitely many copies of the same transition. With observations and
transition labels included, a convenient behavior is

\[
QX=\mathrm{Obs}\times\operatorname{List}(L\times X).
\]

The list factor is polynomial:

\[
\operatorname{List}(L\times X)
\cong\sum_{\ell:\operatorname{List}L}X^{\operatorname{Fin}(|\ell|)}.
\]

The prototype implements this presentation in `listMachine` and `listGSOS`.
Instantiating the configuration step function with the six combinator rules,
or with the additional competing `amb` interactions, fits the same construction.
Internal divergence is represented by infinite unfolding, not by a Lean
function that attempts to normalize the net. An elementary step can be total
even when the computation it generates never terminates.

Observation design matters. A behavior such as \(1+X\) alone remembers
termination and its timing, but not a returned normal form or interface
interaction. Those must be recorded in \(\mathrm{Obs}\), labels, or an
appropriate open-system interface.

Lists retain order and duplicate transitions. They are a presentation of
nondeterminism, not the finite-powerset functor itself. Ordinary powerset
bisimulation requires forgetting this presentation or using an appropriate
quotient/behavior functor. The abstract `GSOSRule` interface permits
non-polynomial functors, but the existing automatic polynomial construction
cannot simply be applied to a powerset functor. Polynomial functors preserve
pullbacks; finite powerset does not, so this is a substantive distinction.

**How the net signature relates to a polynomial.** Lafont's two binary cells
and one nullary cell suggest

\[
P X=X^2+X^2+1.
\]

This describes cell types and their auxiliary slots, with the principal port
distinguished. A slice polynomial

\[
(PX)_i=\sum_{b:B_i}\prod_{e:E_b}X_{s(e)}
\]

can refine this with port sorts, interface types, and restrictions encoded in
indices. This is a useful starting point.

A whole interaction net additionally contains wiring, possible cycles,
boundary ports, and the condition that every port has exactly one wire
endpoint. Principal ports can be wired to other principal ports.
The free monad of the cell polynomial gives trees and substitution; it does
not by itself impose these graph constraints or create arbitrary wiring.
Dependency can enforce constraints through a suitable indexed construction,
but the relevant indices and constructors must be supplied.

A practical first representation would be a finite port graph with a
well-formedness proof, optionally indexed by its boundary interface
\(\Gamma\). Elementary reduction must preserve \(\Gamma\). A more structural
presentation can use the interaction calculus's terms plus equations and
linearity conditions, or explicit gluing operations and their equations.

[Lafont, Section 1.7 and Theorem 1](/home/terence/wingeb/interaction-combinators-lafont.pdf)
uses a stronger notion of translation than an arbitrary interpreter:
cell replacement respects wiring and controls the simulation of reduction.
The construction above establishes inclusion of transition systems.
A corresponding theorem about locality, concurrency, or cost needs more work.
Consequently Turing machines, cellular automata, and other models encoded by
interaction combinators also have representations here, but their stronger
simulation properties do not become proved automatically.

[Mazza's paper](/home/terence/wingeb/denotational-semantics-symmetric-interaction-combinators.pdf)
also deserves a separate qualification: it treats symmetric interaction
combinators, whose universality statement differs from Lafont's original
one. Its relational/geometry-of-interaction semantics is not automatically
the same semantics as a chosen GSOS behavior tree. Identifying the two would
require an adequacy or equivalence theorem.

**Nondeterministic branching and progress are separate choices.**
[Fernández and Khalil, Sections 3–4](/home/terence/wingeb/Interaction_Nets_with_McCarthys_amb.pdf)
give `amb` competing principal ports. It is a readiness-sensitive operator,
not merely a command that guesses one input and blocks on it. The ground
configuration embedding can retain these competing reductions.

To recover the paper's intended angelic/bottom-avoiding behavior, one must
also preserve its interpretation of computation and observation.
Enumerating all reductions and then accepting every arbitrary infinite
scheduling sequence does not automatically establish a must-convergence or
eventual-output guarantee. Any completion/progress convention needed by the
source model must be represented or justified as well.

There is a simple diagnostic for the fairness issue. For two indefinitely
available inputs, binary branching permits a path that always selects the
left input. A fair schedule requires

\[
∀ b\in\{L,R\}\;\forall n\;\exists m\ge n:
\operatorname{schedule}(m)=b.
\]

The prototype proves that always-left fails this property, that alternation
satisfies it, and that _every finite schedule prefix extends to a fair
schedule_. Thus finite observations of scheduling alone do not specify the
required infinite-run guarantee. This is an illustration of the missing
condition, not a formalization of the full published separation theorem.

For partial inputs, even infinitely frequent requests to both ports are
insufficient if a request can block forever. Strict alternation of blocking
reads and an oracle giving finite batch sizes do not solve that problem.
Nor does replacing binary nondeterminism with countable nondeterminism
by itself. The `amb` separation also holds for dynamic dataflow networks:
[Panangaden and Shanbhogue, FSTTCS 1988](https://link.springer.com/chapter/10.1007/3-540-50517-2_90).

The original
[1992 separation paper, Example 2, Section 4, and Theorem 9](https://www.cs.mcgill.ca/~prakash/Pubs/fair_merge_iandc.pdf)
provides a useful positive direction: nonblocking polling can implement
fair merge. Its negative theorem uses closure properties of traces, not
merely the number of alternatives at each step. One obstruction is already
visible in input/output behavior: with inputs \((1^\omega,\epsilon)\),
fair output must be \(1^\omega\); extending the second input to a single
\(2\) requires an output containing \(2\), which cannot extend the already
infinite word \(1^\omega\). Thus adding input need not preserve an available
complete output. Polynomial functoriality on state maps imposes no such
monotonicity requirement on input histories.

Khalil and Fernández also
[report a context-rule extension implementing fair merge](https://drops.dagstuhl.de/storage/16dagstuhl-seminar-proceedings/dsp-vol04241/DagSemProc.04241.1/DagSemProc.04241.1.pdf),
Section 25, printed pages 34–35. This is a short research abstract, not a
complete proof to import. It nevertheless reinforces the distinction between
a limitation of ordinary/`amb` nets and a limitation of arbitrary graph or
coalgebraic execution models.

**What the polling prototype proves.** Give each source a total elementary
step

\[
\operatorname{step}_A:S_A\longrightarrow
\operatorname{Option}(A)\times S_A.
\]

A `none` result is a silent step or a presently empty poll.
It does not decide whether a value will ever arrive. A computation that
diverges before producing its next value can therefore be represented by
arbitrarily many, or infinitely many, silent steps.

The merger keeps both source states and a turn bit. It polls the selected
source once, emits its optional value tagged by its side, and switches turns.
The existing polynomial behavior
\(QX=\operatorname{Option}(A+B)\times X\) suffices.

There is also a small compositional GSOS rule, not just a configuration
embedding. Take two binary operators \(M_L,M_R\), so
\(PX=X^2+X^2\), and \(QX=\operatorname{Option}(A)\times X\).
Writing \(a,b\) for optional observations, its rules are

\[
\begin{aligned}
\rho\bigl(M_L((x,(a,x')), (y,(b,y')))\bigr)&=(a,M_R(x',y)),\\
\rho\bigl(M_R((x,(a,x')), (y,(b,y')))\bigr)&=(b,M_L(x,y')).
\end{aligned}
\]

The prototype implements these in `pollingGSOS` and obtains `pollingAlgebra`
from the existing final bialgebra. Thus the two operators act directly on
final polling behaviors. This signature has no closed terms until source
constants are supplied; the final algebra still gives the desired operations
on behaviors. No change to the GSOS implementation is needed.

The checked theorems `merge_left_output` and `merge_right_output` establish,
with zero-based indexing,

\[
\operatorname{out}(2n)=\operatorname{inl}_*(\operatorname{leftOut}(n)),
\qquad
\operatorname{out}(2n+1)=\operatorname{inr}_*(\operatorname{rightOut}(n)).
\]

These equalities prove preservation of every event occurrence and its order,
with a finite service time for each occurrence. They make no progress
assumption about the _other_ source. After silent events are hidden in the
trace interpretation, all supplied tokens are preserved in order on each
side. We do not implement a total filter into a productive stream of values:
an infinite suffix of silent events must remain representable.

`mergeSemantics` packages this machine through the actual
`universalSemantics` construction. The output theorems concern the concrete
machine's iterated steps; the prototype does not separately prove an
observation theorem relating every such iteration to the library's final
bialgebra morphism, or identifying the executable merger with `pollingAlgebra`.

This is a verified fair service policy for the polling interface. For fixed
source step streams it chooses one interleaving. It is not a proof that its
set of observations is exactly the entire fair-merge relation on opaque,
untimed streams. That stronger claim needs an account of input delivery,
hiding of silent events, admissible executions, and completeness of the
possible interleavings.

In particular, turning opaque streams into these polling sources is not a
free operation definable from `amb`. Exposing input-machine configurations
or introducing a polling primitive supplies additional information/control.
This is why a Turing-computable round-robin simulator and the published
non-implementability result are consistent.

There are other valid approaches within the broad framework: attach an
acceptance predicate such as “every pending token is eventually emitted” to
runs; use proof-carrying fair schedulers; or encode progress obligations with
well-founded counters inside a coinductive behavior. Each adds meaningful
structure. A fairness predicate cannot simply be forgotten and then expected
to reappear from `universalSemantics`.

Mixed least and greatest fixed points are relevant here.
[Fair Reactive Programming, Section 2.5](https://www.cs.mcgill.ca/~prakash/Pubs/fair-reactive.pdf)
uses their alternation to express recurring eventual service.
The repository has both `PolyFix` and `PolyCofix`, so this is a promising
route for types of certified schedules. For example, infinite sequences of
finite nonempty left/right blocks ensure both sides recur. That alone deals
with two inexhaustible inputs; it still does not solve blocking partial
inputs. Almost-sure fairness from random scheduling likewise differs from
fairness on every admissible execution.

**What “pattern runs on matter” would add.**
[Libkind and Spivak, Introduction and Theorem 3.4](https://arxiv.org/abs/2404.16321)
construct

\[
\Xi_{p,q}:\mathfrak m_p\otimes\mathfrak c_q
\longrightarrow\mathfrak m_{p\otimes q},
\]

using the Dirichlet tensor. This is distinct from the distributive law
\(T_PD_Q\to D_QT_P\), whose compositions are substitution/composition.

Their free-monad patterns are well-founded decision trees. In the finitary
case they are finite; the cofree matter can have unending behavior.
Consequently a universal machine can be placed in the matter and observed
by finite patterns such as “perform n steps.” Recovering its entire run
uses the coalgebraic behavior, compatible observations, or an additional
iteration construction. A finite free pattern alone does not provide
unrestricted nonterminating control flow.

Nondeterministic alternatives can be exposed as interactions with an
environment or represented in branching matter. Fairness must still be
specified in that environment, matter, or the allowed executions.
The module law itself selects neither a fair scheduler nor bottom-avoiding
input behavior.

The repository already contains free/cofree polynomial constructions and a
Dirichlet product in [PolyUMorph.lean](../../GebLean/PolyUMorph.lean).
I did not find the paper's module action among the inspected constructions.
Implementing it would be worthwhile for its specific compositional
interaction API, but is unnecessary to establish the execution expressiveness
demonstrated here.

**Validation and the next theorem worth proving.** The following completed:

```text
lake build GebLean.PolyGSOS
lake env lean -DautoImplicit=false -DwarningAsError=true docs/research/InteractionExecution.lean
```

The target build succeeded. The prototype has no sorries or custom axioms.
Its printed axiom checks use only `propext`, `Classical.choice`, and
`Quot.sound`; the two merger output theorems do not use choice.
The example with a permanently silent source and an infinite counter source
also checks by `decide`.

The next substantial task is a small, explicit `Net Γ` representation,
a boundary-preserving reducer, and a simulation theorem connecting the
reducer to the chosen observations. Then one can decide whether the desired
result is a configuration-level simulation, a compositional translation of
open nets, or a fairness-sensitive equivalence of processes. For the latter,
the interface and admissible-run convention should be fixed before choosing
a quotient or proving full abstraction.

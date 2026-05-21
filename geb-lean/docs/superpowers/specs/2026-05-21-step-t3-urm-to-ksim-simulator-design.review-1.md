# Round-1 adversarial review — T3 URM to Ksim simulator

Reviewer: fresh-context `general-purpose` Agent (round 1).
Artefact under review:
[`2026-05-21-step-t3-urm-to-ksim-simulator-design.md`](2026-05-21-step-t3-urm-to-ksim-simulator-design.md).

## Verification log

- Spec § 2 cited line numbers in `GebLean/Utilities/ZeroTestURM.lean`
  (`:89` `URMInstr`, `:122` `URMProgram`, `:143` `URMState`,
  `:155` `step`, `:179` `runFor`, `:213` `runFor_halted_invariant`,
  `:254` `init`): all verified against the file. Pass.
- Spec § 2 cited line numbers in `GebLean/LawvereKSim.lean`
  (`:34` `KMor1`, `:50` `simrec` constructor, `:105` `level`):
  all verified. Pass.
- Spec § 2 cited line numbers in `GebLean/LawvereKSimInterp.lean`
  (`:162` `interp_simrec`, `:180` `simrecVec_zero`,
  `:193` `simrecVec_succ`): all verified. Pass.
- Spec § 2 cited line numbers in `GebLean/Utilities/KArith.lean`
  (`:44` `pred`, `:222` `cond`, `:249` `interp_cond`):
  all verified. Pass.
- Tourlakis 2018 § 0.1.0.17(4) (p. 6) `λx.x ∸ 1 ∈ 𝒦_1`:
  verified in PDF. Pass.
- Tourlakis 2018 § 0.1.0.17(6) (p. 6)
  `switch = λxyz.if x = 0 then y else z`: verified in PDF. Pass.
- Tourlakis 2018 § 0.1.0.37 (pp. 15 – 16) simulation lemma:
  verified in PDF. The lemma's URM has the same five-instruction
  set (`V_i ← c`, `V_i ← V_i + 1`, `V_i ← V_i ∸ 1`,
  `if V_i = 0 goto l₁ else goto l₂`, `stop`) and the same
  past-end self-loop convention. The lemma's conclusion is
  "All the simulating functions are in `𝒦^{sim}_2`", supporting
  `simulate_level ≤ 2`. Pass.
- Tourlakis 2018 § 0.1.0.20 (p. 7)
  `λx.x ≤ a, λx.x < a, λx.x = a ∈ 𝒦_{1,*}`: verified in PDF.
  The proof of equality there constructs `x = a` as the
  conjunction `x ≤ a ∧ a ≤ x` (via § 0.1.0.19's Boolean
  closure), not via a single iterated `pred`. The spec's claim
  that this section grounds "the level-1 predicate
  `pred^k(I) = 0 ⇔ I = k`" is not what the citation supports:
  `pred^k(I) = 0` is equivalent to `I ≤ k`, not `I = k`. Fail;
  see Findings § Blocker B2.
- Tourlakis 2018 § 0.1.0.2 (p. 1) Axt-Heinemann hierarchy
  initial set `𝒦_0` = closure of `{λx.x, λx.x+1}` under
  substitution: verified in PDF. Tourlakis's `𝒦_0` does not
  contain a closed `zero` constant directly; the spec's
  citation grounds the hierarchy bottom but not the
  `succ ∘ zero` construction GebLean uses. Loose; see
  Findings § Minor M1.
- Tourlakis 2018 § 0.1.0.37 initial values: `v_1(0,a) = 0`,
  `v_i(0,a) = a_{i-1}` for input variables, others 0, and
  `I(0,a) = 1`. The GebLean encoding shifts to 0-indexed PC
  (`pc := 0`); the simulator's `baseFamily ⟨0,_⟩ := KMor1.zero`
  is consistent with this shifted convention. Pass (the
  encoding choice is documented in
  `ZeroTestURM.lean:251 – 253`).
- Markdownlint cleanliness of the spec:
  `markdownlint-cli2` on the file reports 0 errors. Pass.
- `KMor1.simrec` constructor type:
  `simrec {a k : ℕ} (i : Fin (k+1)) (h : Fin (k+1) → KMor1 a)
    (g : Fin (k+1) → KMor1 (a + 1 + (k + 1))) : KMor1 (a + 1)`.
  The simrec returns `KMor1 (a + 1)`, not `KMor1 (1 + a)`. Fail
  vs spec § 3.1 declared signature; see Findings § Blocker B3.
- `simrecVec_succ` step-context slot layout: slot 0 = step
  counter, slots `1..a` = params, slot `a + 1 + j` = previous
  component `j`. The spec § 3.4 puts `I_prev` (previous PC) at
  slot `a + 1` and `v_j_prev` at slot `a + 2 + j.val`. Matches
  `simrecVec_succ` because previous PC is component 0 (so slot
  `a + 1 + 0 = a + 1`) and previous register `j` is component
  `j + 1` (so slot `a + 1 + (j + 1) = a + 2 + j`). Pass.
- `KMor1.pcDispatch` reads PC at `ctx (Fin.last n)` (per § 3.5's
  `interp_pcDispatch_match` hypothesis). In the simrec step
  context, the previous PC is at slot `a + 1`, not the last
  slot (`a + numRegs + 1`). The spec does not specify a
  permutation step. Fail; see Findings § Blocker B1.
- The master design's simulator content is in § 7 (specifically
  § 7.1, lines 1909 – 1925), not § 6. § 6 is the catalogue
  index. Misattribution; see Findings § Minor M2.
- Conjunctive vector IH at § 4.2: the IH covers all
  `numRegs + 1` components. The PC step branch for `.jumpZ`
  reads `v_i_prev`; the register-`j` step branches read only
  the previous PC (for `pcDispatch`) and the previous register
  `j`. The conjunctive form is necessary (because the PC branch
  depends on register components), but the spec's claim that
  "each `stepFamily P j` reads the previous values of *every*
  component" is overstated. See Findings § Minor M3.
- Spec § 5 level analysis: `max 0 1 + 1 = 2`. The base sup over
  level-0 components is 0; the step sup, if branches and
  default are all level ≤ 1 and `pcDispatch_level` holds, is
  ≤ 1; then `simrec` adds 1, giving ≤ 2. Pass conditional on
  the resolution of B1 / B2.
- Naming: `def`s `lowerCamelCase`, theorems `snake_case`,
  namespace `UpperCamelCase`. Re-fetched mathlib `naming.html`
  on this round (rules 1 – 6). The spec's enumerated names
  follow these. Pass.
- Style: 100-char line width, 2-space indent, Unicode notation.
  Displayed code blocks in the spec are within budget. Pass.
- Namespace placement: `KArith.lean` declares content under
  `namespace GebLean`, so existing `KMor1.cond` is
  `GebLean.KMor1.cond`. Spec § 6.3 puts the new content in
  `namespace GebLean.KSimURMSimulator`, which would name the
  new helpers `GebLean.KSimURMSimulator.KMor1.pcDispatch`,
  inconsistent with the § 6.4 "extend the existing `KMor1.cond`
  pattern" claim. Fail; see Findings § Serious S1.

## Findings

### Blocker

1. **`pcDispatch` reads the wrong context slot for the simrec
   layout.** § 3.5 specifies
   `(KMor1.pcDispatch size branches default).interp ctx
    = (branches k).interp (Fin.init ctx)` under
   `ctx (Fin.last n) = k.val`; the PC is read at the last
   context slot. But in § 3.4's `stepFamily`, the step context
   has slot 0 for the iteration counter, slots `1..a` for
   inputs, slot `a + 1` for the previous PC, and slots
   `a + 2..` for previous registers. Slot `a + 1` is not the
   last slot (which is `a + numRegs + 1`). An implementer
   reading § 3.4 and § 3.5 together would either find that the
   type-check succeeds but the dispatch reads the last
   register's previous value as if it were the PC, producing a
   wrong simulator; or have to invent an unspecified adaptor.

   *Author response — fix.* Relabel the simrec component vector:
   components `0, …, numRegs − 1` hold register values
   `regs 0, …, regs (numRegs − 1)`; component `numRegs` (the
   last) holds the PC. Output index becomes
   `P.outputReg.castSucc : Fin (P.numRegs + 1)`. The previous-PC
   slot in the step context is then `a + 1 + numRegs`, the
   last slot, lining up with `pcDispatch`'s `Fin.last n` read.
   Edits applied in § 3.2 (component layout), § 3.3 (base family
   reordering), § 3.4 (step-context layout and helper-projection
   offsets), § 4.1 (output projection now via `castSucc`),
   § 4.2 (component indexing in the IH).

2. **`pred^k(I) = 0 ⇔ I = k` is false; the equivalence is
   `pred^k(I) = 0 ⇔ I ≤ k`.** § 11.1's gloss on Tourlakis
   § 0.1.0.20 and § 3.5's surrounding prose treat
   `pred^k(PC) = 0` as the equality test "PC = k". Iterated
   truncated decrement vanishes once the input is `≤ k`, not
   exactly at `k`. As a consequence, the top-down recursion
   displayed in § 3.5

   ```text
   pcDispatch (k+1) branches default :=
     cond ∘ ⟨pred^k(PC), branches ⟨k, _⟩,
             pcDispatch k (branches ∘ castSucc) default⟩
   ```

   does not implement the intended dispatch: when `PC < k` it
   still selects `branches k` (because `pred^k(PC) = 0`), not
   `branches PC`. The bottom-up form (test `PC = 0` first, then
   shift by `pred` and recurse) does implement the intended
   dispatch; the spec's "either form yields the same
   interpretation" sentence misleads. An implementer following
   the displayed pseudocode would build a wrong dispatcher.

   *Author response — fix.* Drop the misleading top-down
   pseudocode block from § 3.5. Replace with prose specifying
   the bottom-up recursion: base case `size = 0` returns
   `default` lifted to arity `n + 1` via projection (with the
   K^sim realisation explicit per S2); recursive case
   `size + 1` introduces one `cond` test for PC = 0 selecting
   `branches ⟨0, _⟩`, with the else-branch recursing on
   `pcDispatch size (branches ∘ Fin.succ) default`
   pre-composed with a `pred`-shift of the PC slot. The
   bottom-up dispatch tests `cond(PC, branches[0], cond(PC, …
   shifted))`-style at level 1: each `cond` test reads the
   current PC slot (level 0 projection); the chained recursion
   does not bump level. § 11.1's gloss on § 0.1.0.20 corrected
   to cite the `λx.x ≤ a` predicate at level 1, which is what
   `pred^k(PC) = 0` actually computes.

3. **Type-level mismatch `KMor1 (1 + a)` vs `KMor1 (a + 1)`.**
   § 3.1 declares `simulate {a : ℕ} (P : URMProgram a) :
   KMor1 (1 + a)`, but `KMor1.simrec` produces a term of type
   `KMor1 (a + 1)`. In Lean's `Nat`, `1 + a` and `a + 1` are
   propositionally but not definitionally equal.

   *Author response — fix.* Public signature changed to
   `simulate {a : ℕ} (P : URMProgram a) : KMor1 (a + 1)`,
   matching `KMor1.simrec`'s return type. `Fin.cons y v` has
   type `Fin (a + 1) → ℕ` directly, so no cast is needed.
   Edits applied in § 1, § 3.1, § 4.1, § 5.

### Serious

1. **Namespace placement contradicts § 6.4's "extend existing
   `KMor1.*` pattern" claim.** § 6.3's outline puts the new
   content under `namespace GebLean.KSimURMSimulator`, yielding
   `GebLean.KSimURMSimulator.KMor1.pcDispatch` etc., while
   § 6.4 says these declarations "extend the existing
   `KMor1.cond` pattern in `KArith.lean`", whose existing names
   are `GebLean.KMor1.cond`.

   *Author response — fix.* Split namespace usage: the new
   `KMor1.*` helpers (`pcDispatch`, `natK`, `natK'`) declared
   inside `namespace GebLean` directly, matching the existing
   `KMor1.cond` pattern in `KArith.lean`; the
   simulator-specific non-`KMor1` definitions (`baseFamily`,
   `stepFamily`, `simulate`, `simulate_step_match`,
   `simulate_interp`, `simulate_level`) declared inside
   `namespace GebLean.KSimURMSimulator`. Edits applied in
   § 6.3 (outline), § 6.4 (rationale paragraph).

2. **`pcDispatch 0 _ default := default ∘ Fin.init` is not a
   K^sim term.** § 3.5's base case writes `default ∘ Fin.init`.
   `KMor1` has no constructor for general function composition
   over the context; the K^sim realisation of "drop the last
   context slot" is
   `KMor1.comp default
     (fun i : Fin n => KMor1.proj (Fin.castSucc i))`.

   *Author response — fix.* Replace `default ∘ Fin.init` in
   § 3.5 with the K^sim form
   `KMor1.comp default (fun i : Fin n => KMor1.proj
   (Fin.castSucc i))`. Same substitution in the
   `interp_pcDispatch_*` lemma RHS prose (the interp side is
   still a Nat-side function `Fin.init ctx`; the K^sim term on
   the LHS is the explicit composition). The displayed lemma
   statements thus refer to the interpretation-side
   `Fin.init ctx` while the underlying term is the explicit
   `KMor1.comp`-projection composition.

### Minor

1. **Tourlakis § 0.1.0.2 citation grounds the hierarchy, not
   the `succ ∘ zero` construction.** The cited subsection
   defines the hierarchy with initial functions
   `{λx.x, λx.x+1}`; it does not contain a closed `zero`
   constant.

   *Author response — fix.* Tighten the § 11.1 citation for
   `natK` to point to the GebLean precedent
   `KMor1.one : KMor1 0` at `KArith.lean:31` (the closed
   constant `1` constructed analogously) and to Tourlakis
   § 0.1.0.2 for the level-0 closure principle, rather than
   for the specific `succ ∘ zero` construction.

2. **§ 1 misattributes the master-design section.** The
   simulator material is § 7, not § 6.

   *Author response — fix.* § 1 corrected to read "Re-spec of
   master design § 7" with the parenthetical pointer
   "(specifically § 7.1, K^sim simulator for URM)". The
   re-spec target in `2026-05-16-er-to-k-via-cslib-urm-design.md`
   is also that document's § 6 (which carries the same
   simulator content; the T1/T2 spec renumbered).

3. **§ 4.2 overstates the read pattern of step families.**
   Register step families read only the previous PC and the
   previous register `j`; only the PC step family reads other
   registers' previous values.

   *Author response — fix.* § 4.2 rationale paragraph
   corrected: "The PC step family reads the previous values of
   the registers (via the `.jumpZ` branch on `v_i_prev`); each
   register-`j` step family reads only the previous PC (for
   the `pcDispatch` test) and the previous register `j`. The
   conjunctive form remains necessary because the PC's
   cross-component read forces a joint IH."

4. **§ 1's "T4 / T5 / T6" partition is unanchored to
   master-design step numbers.**

   *Author response — fix.* § 1 and § 8 amended to anchor each
   deferred item to the specific master-design step index:
   `boundExprK` and the level-2 K^sim composites to master
   § 8.1 – § 8.3 (T4); `erToK` assembly and
   `erToKFunctor` to master § 9 (T5); strict iso to master
   § 11 (T6).

5. **`baseFamily`'s `Fin a` index disambiguation.** The
   variable `i : Fin a` in the `match … with | some i => …`
   line is named identically to its outer-scope reuse.

   *Author response — fix.* § 3.3 now opens with one
   clarifying sentence: "In the `some i` branch, `i : Fin a`
   is the input slot index returned by `List.find?`;
   `KMor1.proj i` has type `KMor1 a`, matching the
   `baseFamily` return type." Plus an inline comment in the
   pseudocode disambiguating `i` from `r : Fin P.numRegs`.

### Cosmetic-taste

1. **Per-task LOC estimates in § 9 are not load-bearing.**

   *Author response — reject-as-cosmetic-taste.* The per-task
   LOC estimates inform sub-agent task dispatching by giving
   each implementer a budget; the budget is a known weak
   estimate, but a weak estimate is better than no estimate
   for the sake of scoping subagent prompts during plan
   execution. Keep.

2. **§ 3.5's "either form yields the same interpretation"
   sentence conflates implementation choice with semantic
   equivalence without proof.**

   *Author response — fix (subsumed by B2).* The sentence is
   removed as part of B2's fix; § 3.5's revised prose names
   the bottom-up recursion as the reference implementation
   and lets the `interp_pcDispatch_*` lemmas carry the
   behavioural contract.

3. **Module-docstring section enumeration absent from § 6.3.**

   *Author response — fix.* § 6.3's outline expanded to list
   the mathlib `doc.html` section ordering verbatim
   (`# Title`, summary, `## Main definitions`,
   `## Main statements`, optional `## Notation`, optional
   `## Implementation notes`, `## References`, `## Tags`).

4. **`K^sim_{1,*}` notation appears only once.**

   *Author response — fix.* § 11.1's § 0.1.0.20 entry now
   carries a parenthetical gloss "(the predicate
   sub-class of `K^sim_1`, per Tourlakis § 0.1.0.18 – 0.1.0.20)".
   No other call site, so a one-time gloss suffices.

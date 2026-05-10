# Adversarial review cycle 14 — author responses

Review dispatched: fresh-context Agent.

## Serious

### S1 — Stale "branch-protection rules" cross-reference

**Finding.** Cycle 13's terminology fix (renaming "branch-
protection rules" to "repository protection rules" with the
Rulesets / Tag protection split) was applied at item 17a but
not propagated to the earlier cross-reference at the empirical-
verifications appendix (line 1060). That cross-reference still
said "GitHub branch-protection rules" pointing at item 17a,
where the reader now finds different language.

**Response: fixed.** Update the cross-reference at line 1060
to "GitHub repository protection rules" matching item 17a.

## Minor

### M1 — Bare-name push form is ambiguous if a branch and tag share names

**Finding.** Item 17 listed `git push origin <name>` as one of
three valid forms; git resolves bare names against both branch
and tag namespaces and refuses if both exist. The project's
naming convention prevents this in practice (no `cutover-*`
branch exists), but the spec didn't state the precondition.

**Response: fixed.** Drop the bare-name form from item 17.
Keep only the two unambiguous forms (`git push origin tag
<name>` and the wildcard refspec) and add a one-sentence
explanation of why the bare-name form is avoided.

### M2 — "Legacy repos" framing for Tag protection rules is imprecise

**Finding.** The phrase "on legacy repos, a Tag protection
rule under Settings → Tags" implies a per-repo legacy flag.
GitHub has deprecated Tag protection rules in favour of
Rulesets but they remain available on most repositories as a
deprecated alternative.

**Response: fixed.** Rephrase: "Tag protection rules under
Settings → Tags is a deprecated alternative still available
on most repositories; either mechanism suffices, but the
Ruleset is preferred." This matches GitHub's own deprecation
framing.

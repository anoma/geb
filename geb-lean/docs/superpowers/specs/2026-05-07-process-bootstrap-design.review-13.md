# Adversarial review cycle 13 — author responses

Review dispatched: fresh-context Agent.

## Serious

### S1 — Stale parenthetical in item 17 references a now-removed allowlist entry

**Finding.** Item 17 still says the wildcard refspec is
"mandated by the `block-mutating-git` hook's allowlist", but
cycle 12 dropped the tag-push allowlist entry. § Hooks now
explicitly states no tag-push allowlist exists. The
parenthetical is internally inconsistent with the rest of the
spec.

**Response: fixed.** Drop the stale parenthetical. The user
chooses any working form (`git push origin
cutover-2026-MM-DD`, `git push origin tag
cutover-2026-MM-DD`, or the wildcard
`git push origin 'refs/tags/cutover-*:refs/tags/cutover-*'`)
since the operation is user-direct and the hook does not
intercept user-terminal commands.

## Minor

### M1 — "Branch-protection rules" terminology doesn't cover tag deletion

**Finding.** GitHub's Branch protection rules feature targets
branches; tag deletion protection lives under Rulesets
(modern) or Tag protection rules (legacy). The spec's "the
branch-protection rules" reference for tag deletion would
mislead an implementer looking in the wrong UI.

**Response: fixed.** Item 17a is rewritten:

> GitHub repository protection rules are configured: on
> `main`, branch-protection rules forbid force-pushes and
> branch deletion; on tags matching `cutover-*`, a Ruleset
> (under Repository settings → Rulesets) — or, on legacy
> repos, a Tag protection rule under Settings → Tags —
> forbids deletion.

The same language is used in item 17's reference to "the
branch-protection rules" being amended to "the repository
protection rules (item 17a)".

## Cosmetic-taste

### C1 — Smoke-test case (e) is functionally redundant but acts as a regression pin

**Response: rejected (cosmetic-taste, with rationale
agreement).** Reviewer agrees. Case (e) is kept as a
deliberate regression pin against future drift toward
re-adding a tag-push allowlist entry; its redundancy with the
default-deny default is the point.

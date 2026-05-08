# Adversarial review cycle 10 — author responses

Review dispatched: fresh-context Agent.

## Blocker

### B1 — Item 12(c) positive smoke test uses a refspec the allowlist would block

**Finding.** My cycle-9 fix to item 12 added a positive
smoke-test command
`git push origin 'refs/tags/cutover-test:refs/tags/cutover-test'`,
but the allowlist's literal-token equality rule blocks any
refspec other than exactly
`refs/tags/cutover-*:refs/tags/cutover-*`. The "positive" test
as written can't pass — it's effectively another instance of
the negative test. This is internal contradiction.

**Response: fixed (with apology — the spec's own
literal-token rule, which I introduced, undermined a smoke
test I introduced in the very next cycle).** Rewrite item
12(c) and add a third tag-push smoke-test entry:

- **(c) revised**: with a throwaway local `cutover-test` tag
  in place, `git push origin
  'refs/tags/cutover-*:refs/tags/cutover-*'` is not blocked
  by the hook (positive test of the tag-push allowlist
  branch). The push then propagates the throwaway tag to the
  remote; the test deletes the remote tag afterward via a
  manual user step (which lies outside the hook's scope, per
  the human-gate rule).
- **(d) revised**: `git push origin
  'refs/tags/v1.0.0:refs/tags/v1.0.0'` (a non-`cutover-*`
  tag-push form) is blocked (negative test).
- **(e) new**: `git push origin
  'refs/tags/cutover-test:refs/tags/cutover-test'` (a
  specific-name form within the cutover prefix) is blocked
  (negative test of the literal-token rule itself, ensuring
  no glob-expansion shortcut sneaks through).

This third entry is the explicit guard against future drift
where someone might "improve" the hook by adding glob
matching. The smoke tests now exercise both the allowed form
and two distinct rejection paths.

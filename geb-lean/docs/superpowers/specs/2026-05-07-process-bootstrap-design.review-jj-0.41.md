# jj 0.41 upgrade — research and spec changes

Triggered by: jj 0.41 release announcement (user upgraded local
install). Per the spec's "verify agent claims against
authoritative sources" rule, every jj-related claim was
re-checked against the v0.41 release notes and the current
docs (and against the locally-installed `jj 0.41.0` for
empirical claims).

## Changes propagated to the spec

### Material simplification: `remotes.<name>.fetch-tags`

**v0.41 release note (verbatim from
<https://github.com/jj-vcs/jj/releases/tag/v0.41.0> via the
docs at <https://docs.jj-vcs.dev/latest/config/>):** *"New
`remotes.<name>.fetch-bookmarks`/`fetch-tags` options to
configure default fetch targets. The value is a string
pattern that matches the names of the bookmarks and tags to
fetch."*

**Spec impact:** the cycles-6-through-9 chain of fixes around
the cutover-tag fetch (the explicit
`git fetch origin 'refs/tags/cutover-*:refs/tags/cutover-*'`
form, the corresponding `block-mutating-git` allowlist entry,
the on-boarding step's "subsequent fetches will only fetch
included tags" caveat) was driven by jj 0.40's limitation.
With v0.41:

- Set `jj config set --repo remotes.origin.fetch-tags 'glob:cutover-*'`
  once (same per-repo config layer as `git.private-commits`).
- `jj git fetch --remote origin` thereafter mirrors the
  cutover tag(s) automatically.
- The explicit raw-`git fetch` form is no longer needed.
- The corresponding `block-mutating-git` allowlist entry is
  removed.
- The "Refspec matching semantics" paragraph is rewritten
  around the surviving allowlisted refspec
  (`refs/pull/*/head:*` for `gh pr checkout`).

### `git clean -xdf` hint removal

**Empirical finding (jj 0.41.0):** `jj git init --colocate`
no longer prints `Hint: Running 'git clean -xdf' will remove
'.jj/'!`. The warning is now documented entirely in
`docs/process.md` § jj rather than relying on jj's runtime
hint. The empirical-verifications appendix records both the
0.40 behavior (hint present) and the 0.41 behavior (hint
removed).

### Re-verifications

The following claims were re-checked under jj 0.41.0; all
behavior persists from 0.40:

- `jj git init --colocate` creates `.jj/.gitignore`
  containing `/*\n` (3 bytes).
- `jj git push` has no `--tag` flag.
- `jj git` has no `tag` subcommand (subcommands: `clone`,
  `fetch`, `init`, `push`, `remote`).
- `jj git push` is `--force-with-lease`-equivalent by
  default.
- `git.private-commits` still applies at push time;
  exemptions for already-pushed and immutable commits remain
  documented.

### Version-pin updates

All "jj 0.40+" references in the spec are updated to
"jj 0.41+". The empirical-verifications appendix renames
"§ jj 0.36–0.40 behavior changes" to "§ jj 0.36–0.41 behavior
changes" and adds the v0.41 entries.

## Changes considered but rejected

The v0.41 release notes also included:

- **`jj git push --all`/`--tracked`/`-r REVSETS` no longer
  fails on private/conflicts**: re-stated from v0.38; we don't
  use these flags. Individual bookmark pushes are unaffected.
- **`jj git clone` bookmark patterns saved to repo settings
  file**: we don't use `jj git clone` with bookmark patterns.
- **`--pattern` default for `jj file search` changed to
  `regex:`**: we don't use `jj file search`.
- **Template `Operation.tags()` deprecated → `.attributes()`**:
  we don't write jj templates.
- **`JJ_PAGER` overrides `ui.pager`**: irrelevant.
- **`jj fix` line-range formatting**: irrelevant.

None affect the spec.

## Convergence after these changes

The changes above are material (a whole on-boarding step and
allowlist branch removed; one runtime-hint paragraph
reframed) but follow directly from the v0.41 release notes
and empirical verification. They have not been put through a
fresh adversarial-review cycle yet; per the discipline, that
should be done. (The spec's own "no fixed cycle cap" rule
applies: another cycle is appropriate when the artefact has
changed materially.)

The spec was at 1625 lines before these changes; it is at
1645 lines after. The structural design is unchanged.

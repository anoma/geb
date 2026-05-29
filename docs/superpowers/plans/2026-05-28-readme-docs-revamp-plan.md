# README and documentation-index revamp Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps
> use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Turn the monorepo root `README.md` into a hand-authored
documentation index, relocate the obsolete Common Lisp material under
`docs/common-lisp/`, give `geb-idris` a documentation index, and leave
the Common Lisp generator emitting into `docs/common-lisp/` so a rebuild
produces no diff.

**Architecture:** A sequence of single-concept commits. Each commit is a
pure file move, a pure deletion, a focused generator code change, a
verbatim commit of generator output, or a skeleton-file creation. Moves
precede creation of the new root `README.md` so version control records
the old manual's relocation as a rename. The Common Lisp generator is
run once, in-session under Roswell, to produce and validate
`docs/common-lisp/manual.md`.

**Tech Stack:** `jj` (colocated, VCS), Roswell SBCL 2.4.10 + quicklisp +
mgl-pax (Common Lisp documentation generator), `markdownlint-cli2`,
`doctoc`.

---

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Conventions for every task](#conventions-for-every-task)
- [Task 0: Baseline verification](#task-0-baseline-verification)
- [Task 1: Relocate the generated Common Lisp manual (pure rename)](#task-1-relocate-the-generated-common-lisp-manual-pure-rename)
- [Task 2: Relocate the Common Lisp documentation sources](#task-2-relocate-the-common-lisp-documentation-sources)
- [Task 3: Delete the redundant plain-text README](#task-3-delete-the-redundant-plain-text-readme)
- [Task 4: Retarget the documentation generator](#task-4-retarget-the-documentation-generator)
- [Task 5: Regenerate and validate the manual](#task-5-regenerate-and-validate-the-manual)
- [Task 6: Create the geb-idris documentation index](#task-6-create-the-geb-idris-documentation-index)
- [Task 7: Create the root README index](#task-7-create-the-root-readme-index)
- [Task 8: Final verification](#task-8-final-verification)

<!-- END doctoc -->

## Conventions for every task

- Work happens on the existing bookmark `docs/readme-docs-revamp`. The
  spec commits are already present; tasks below append commits.
- File moves use plain `mv` (filesystem); `jj` snapshots the change. Do
  not use `git mv` (the `block-mutating-git.sh` hook gates raw mutating
  git).
- Commit pattern after staging a task's changes:

  ```bash
  jj commit -m "<message>"
  jj bookmark set docs/readme-docs-revamp -r @-
  ```

- No `.lean` files are touched, so the Lean pre-commit triad does not
  apply. Markdown that this plan authors (`geb-idris/docs/index.md`,
  root `README.md`) is linted before its commit with:

  ```bash
  markdownlint-cli2 --config geb-lean/.markdownlint-cli2.jsonc --no-globs '<path>'
  ```

- `docs/common-lisp/manual.md` is generator output; it is not linted or
  reformatted.
- No `jj git push` occurs anywhere in this plan; pushing is a separate,
  user-gated step after the whole plan is reviewed.

## Task 0: Baseline verification

**Files:** none (verification only).

- [ ] **Step 1: Confirm the working copy is clean and on the branch**

Run:

```bash
jj status
jj log -r 'main..@-' --no-graph -T 'description.first_line() ++ "\n"'
```

Expected: `jj status` reports no uncommitted changes; the log lists the
spec commits on `docs/readme-docs-revamp` (the most recent being the
spec's HTML-handling revision).

- [ ] **Step 2: Record the pre-existing generator drift as the baseline**

Run:

```bash
cp README.md /tmp/baseline-README.md
cp README /tmp/baseline-README.plain
wc -l README README.md
```

Expected: `README` is 4553 lines, `README.md` is 6118 lines. These
backups are a safety net for the move steps; the generator output
committed in Task 5 supersedes them.

- [ ] **Step 3: Reference-integrity check before any move**

Confirm nothing links to the root `README`/`README.md` in a way the
relocation would silently break:

```bash
grep -rIn --exclude-dir=.git --exclude-dir=.jj --exclude-dir=.lake \
  -e ']\(\.\./README\(\.md\)\?\)' -e ']\(README\(\.md\)\?\)' -e ']\(\./README' \
  geb-idris/docs geb-lean/docs geb-agda 2>/dev/null || echo "no inbound links in subproject docs"
grep -rIn --exclude-dir=.git --exclude-dir=.jj 'README' \
  geb-lean/README.md geb-idris/README.md geb-agda/README.md 2>/dev/null
```

Expected: the subproject `docs/` trees contain no links to the root
README files. The three subproject `README.md` files link to
`../README.md` (the new index satisfies this) and not to the moving
file's new location. If any file links to the root README's *content*
(rather than the path the new index occupies), note it before
proceeding.

## Task 1: Relocate the generated Common Lisp manual (pure rename)

**Files:**

- Move: `README.md` -> `docs/common-lisp/manual.md`

- [ ] **Step 1: Create the target directory and move the file**

Run:

```bash
mkdir -p docs/common-lisp
mv README.md docs/common-lisp/manual.md
```

- [ ] **Step 2: Verify the move is a pure rename**

Run:

```bash
jj diff --stat
```

Expected: exactly one rename, `README.md => docs/common-lisp/manual.md`,
with no content delta (jj shows it as a rename; if it shows a
delete+add, confirm the byte content is unchanged with
`diff /tmp/baseline-README.md docs/common-lisp/manual.md`, which must be
empty). The repository root now has no `README.md`.

- [ ] **Step 3: Commit**

```bash
jj commit -m "docs: relocate generated Common Lisp manual to docs/common-lisp/manual.md

Pure rename of the root README.md (generated Common Lisp manual) into
docs/common-lisp/. Content is unchanged; Task 5 regenerates it from the
retargeted generator."
jj bookmark set docs/readme-docs-revamp -r @-
```

## Task 2: Relocate the Common Lisp documentation sources

**Files:**

- Move: `docs/documentation.lisp` -> `docs/common-lisp/documentation.lisp`
- Move: `docs/glossery.lisp` -> `docs/common-lisp/glossery.lisp` (sic;
  the filename is misspelled in the tree, preserve it verbatim)
- Move: `docs/package.lisp` -> `docs/common-lisp/package.lisp`
- Move: `docs/maintainers-guide.org` -> `docs/common-lisp/maintainers-guide.org`
- Modify: `geb.asd:184`

- [ ] **Step 1: Move the four source files**

Run:

```bash
mv docs/documentation.lisp  docs/common-lisp/documentation.lisp
mv docs/glossery.lisp       docs/common-lisp/glossery.lisp
mv docs/package.lisp        docs/common-lisp/package.lisp
mv docs/maintainers-guide.org docs/common-lisp/maintainers-guide.org
```

- [ ] **Step 2: Update the `geb/documentation` system pathname**

Edit `geb.asd`. Change the `geb/documentation` system's pathname (line
184):

```lisp
  :pathname "docs/"
```

to:

```lisp
  :pathname "docs/common-lisp/"
```

This is the only line that changes; the three `.lisp` files are
`:serial` components named `package`, `glossery`, `documentation` and
load in that order from the new pathname. `maintainers-guide.org` is not
an ASDF component, so its move has no build effect.

- [ ] **Step 3: Verify `geb/documentation` still loads from the new path**

Run:

```bash
timeout 600 ros run \
  -e '(asdf:load-asd (truename "geb.asd"))' \
  -e '(ql:quickload :geb :silent t)' \
  -e '(ql:quickload :geb/documentation :silent t)' \
  -e '(format t "~%DOC-SYSTEM-LOAD-OK~%")' \
  -q 2>&1 | tail -3
```

Expected: ends with `DOC-SYSTEM-LOAD-OK` and no error. (First run
compiles; allow a few minutes.)

- [ ] **Step 4: Commit**

```bash
jj commit -m "docs: relocate Common Lisp doc sources to docs/common-lisp/

Move documentation.lisp, glossery.lisp, package.lisp and
maintainers-guide.org into docs/common-lisp/, and point the
geb/documentation ASDF system's :pathname at the new directory. The
serial load order of the three components is unchanged."
jj bookmark set docs/readme-docs-revamp -r @-
```

## Task 3: Delete the redundant plain-text README

**Files:**

- Delete: `README`

- [ ] **Step 1: Delete the file**

Run:

```bash
rm README
```

- [ ] **Step 2: Verify nothing else references it**

Run:

```bash
grep -rIn --exclude-dir=.git --exclude-dir=.jj --exclude-dir=.lake \
  -e '\bREADME\b' geb.asd Makefile .github/ 2>/dev/null | grep -v 'README\.md' || echo "no references"
```

Expected: `no references` (the plain `README` is not referenced by the
build, Makefile, or CI). `jj diff --stat` shows a single deletion.

- [ ] **Step 3: Commit**

```bash
jj commit -m "docs: delete redundant plain-text README

The markdown manual at docs/common-lisp/manual.md supersedes the
plain-text generator output, which is no longer emitted after the
generator retarget."
jj bookmark set docs/readme-docs-revamp -r @-
```

## Task 4: Retarget the documentation generator

**Files:**

- Modify: `docs/common-lisp/documentation.lisp` (the `build-docs`
  function, near the end of the file)
- Modify: `.gitignore`

- [ ] **Step 1: Rewrite `build-docs` to write markdown directly to `manual.md`**

Replace the existing `build-docs` definition in
`docs/common-lisp/documentation.lisp`:

```lisp
(defun build-docs ()
  (mgl-pax:update-asdf-system-readmes
   @index :geb
   :formats '(:markdown :plain))
  (mgl-pax:update-asdf-system-html-docs
   @index :geb
   :target-dir (asdf/system:system-relative-pathname :geb "docs/")
   :pages (geb-pages)))
```

with:

```lisp
(defun build-docs ()
  (mgl-pax:document
   @index
   :format :markdown
   :pages `((:objects (,@index)
            :output (,(asdf:system-relative-pathname
                        :geb "docs/common-lisp/manual.md")
                     :if-exists :supersede :if-does-not-exist :create)
            :source-uri-fn ,(pax:make-github-source-uri-fn
                              :geb "https://github.com/anoma/geb"))))
  (mgl-pax:update-asdf-system-html-docs
   @index :geb
   :target-dir (asdf:system-relative-pathname
                 :geb "docs/common-lisp/html/")
   :pages (geb-pages)))
```

This writes the markdown manual directly to
`docs/common-lisp/manual.md` through a page with an explicit `:output`
(so it never creates a root `README.md`), drops the `:plain` output, and
redirects HTML into `docs/common-lisp/html/`. The `:source-uri-fn`
mirrors the HTML page so source links resolve. This was confirmed to
produce the full manual when run during planning.

- [ ] **Step 2: Ignore the generated HTML output**

Add to `.gitignore` (after the existing `build/` line):

```gitignore
/docs/common-lisp/html/
```

The HTML output is generated, never committed (no generated HTML is
tracked under `docs/` today); the ignore keeps a generator run from
leaving untracked files.

- [ ] **Step 3: Verify the file still loads**

Run:

```bash
timeout 600 ros run \
  -e '(asdf:load-asd (truename "geb.asd"))' \
  -e '(ql:quickload :geb :silent t)' \
  -e '(ql:quickload :geb/documentation :silent t)' \
  -e '(format t "~%RETARGET-LOAD-OK~%")' \
  -q 2>&1 | tail -3
```

Expected: ends with `RETARGET-LOAD-OK` and no error (the rewritten
`build-docs` compiles).

- [ ] **Step 4: Commit**

```bash
jj commit -m "docs: retarget Common Lisp generator output to docs/common-lisp/

Rewrite build-docs to write the markdown manual directly to
docs/common-lisp/manual.md via a page with an explicit :output (so it
never recreates a root README.md), drop the plain-text format, and
redirect HTML output into docs/common-lisp/html/. Ignore that HTML
directory so a generator run leaves no untracked files."
jj bookmark set docs/readme-docs-revamp -r @-
```

## Task 5: Regenerate and validate the manual

**Files:**

- Modify (regenerate): `docs/common-lisp/manual.md`

- [ ] **Step 1: Run the retargeted generator**

Run:

```bash
timeout 600 ros run \
  -e '(asdf:load-asd (truename "geb.asd"))' \
  -e '(ql:quickload :geb :silent t)' \
  -e '(ql:quickload :geb/documentation :silent t)' \
  -e '(ql:quickload :mgl-pax/navigate :silent t)' \
  -e '(ql:quickload :mgl-pax/document :silent t)' \
  -e '(funcall (uiop:find-symbol* :build-docs :geb-docs/docs))' \
  -e '(format t "~%BUILD-DOCS-OK~%")' \
  -q 2>&1 | tail -3
```

Expected: ends with `BUILD-DOCS-OK`. Late symbol resolution
(`uiop:find-symbol*`) avoids read-time package errors. `build-docs`
writes `docs/common-lisp/manual.md` and HTML into
`docs/common-lisp/html/` (the latter is gitignored).

- [ ] **Step 2: Confirm the working tree shows only the manual change**

Run:

```bash
jj status
```

Expected: the only listed change is `docs/common-lisp/manual.md`
(modified). No `docs/common-lisp/html/` entries appear (gitignored), and
no root `README.md` was created. If anything else appears, stop and
investigate.

- [ ] **Step 3: Sanity-check the regenerated manual**

Run:

```bash
head -5 docs/common-lisp/manual.md
grep -c '^#' docs/common-lisp/manual.md
```

Expected: begins with the `# The GEB Manual` heading (after mgl-pax
anchor lines); a positive heading count. The content is the current
Common Lisp manual.

- [ ] **Step 4: Commit the regenerated manual**

```bash
jj commit -m "docs: regenerate Common Lisp manual from retargeted generator

Replace the relocated stale manual with the current generator output.
This reconciles pre-existing drift (a manual edit, source updates, and
mgl-pax version changes) so a rebuild is a no-op."
jj bookmark set docs/readme-docs-revamp -r @-
```

- [ ] **Step 5: Validate idempotency (zero diff on rebuild)**

Re-run the generator and confirm it changes nothing:

```bash
timeout 600 ros run \
  -e '(asdf:load-asd (truename "geb.asd"))' \
  -e '(ql:quickload :geb :silent t)' \
  -e '(ql:quickload :geb/documentation :silent t)' \
  -e '(ql:quickload :mgl-pax/navigate :silent t)' \
  -e '(ql:quickload :mgl-pax/document :silent t)' \
  -e '(funcall (uiop:find-symbol* :build-docs :geb-docs/docs))' \
  -e '(format t "~%REBUILD-OK~%")' \
  -q 2>&1 | tail -3
jj status
```

Expected: `REBUILD-OK`, and `jj status` reports no changes (the
committed `manual.md` equals the generator's output, so a rebuild
produces no diff). If `manual.md` shows as modified, the output is not
deterministic; stop and investigate before proceeding.

## Task 6: Create the geb-idris documentation index

**Files:**

- Create: `geb-idris/docs/index.md`

- [ ] **Step 1: Write the index file**

Create `geb-idris/docs/index.md` with exactly:

```markdown
# geb-idris documentation

Documentation for the Idris-2 implementation of Geb. For the
implementation overview see [`../README.md`](../README.md); for worked
examples see [`../EXAMPLES.md`](../EXAMPLES.md).

## Documents

- [`geb-syllabus.md`](geb-syllabus.md) — Geb reading group syllabus.
- [`mldirichf-generalization.md`](mldirichf-generalization.md) — MLDirichF
  generalization plan.
- [`profunctor-end-characterization.md`](profunctor-end-characterization.md)
  — characterizing ends of polynomial profunctors.
- [`twisted-arrow-copresheaf-analysis.md`](twisted-arrow-copresheaf-analysis.md)
  — copresheaves versus presheaves on twisted-arrow categories.
```

The labels are derived from each file's existing `#` title. The file has
a single `##` heading, so no doctoc table of contents is required.

- [ ] **Step 2: Lint and verify link targets exist**

Run:

```bash
markdownlint-cli2 --config geb-lean/.markdownlint-cli2.jsonc --no-globs 'geb-idris/docs/index.md'
ls geb-idris/README.md geb-idris/EXAMPLES.md \
   geb-idris/docs/geb-syllabus.md \
   geb-idris/docs/mldirichf-generalization.md \
   geb-idris/docs/profunctor-end-characterization.md \
   geb-idris/docs/twisted-arrow-copresheaf-analysis.md
```

Expected: markdownlint reports `0 error(s)`; all six listed paths exist.

- [ ] **Step 3: Commit**

```bash
jj commit -m "docs(geb-idris): add documentation index skeleton

Index the four existing Idris documentation files with navigational
labels derived from their titles, and point to the implementation
overview and examples. No new explanatory content."
jj bookmark set docs/readme-docs-revamp -r @-
```

## Task 7: Create the root README index

**Files:**

- Create: `README.md`

- [ ] **Step 1: Write the new root README index**

Create `README.md` with exactly the following (the doctoc markers are
present so Step 2 can insert the table of contents):

```markdown
# Geb

Geb is a categorical programming language whose first-class notions
include "programming language" itself. Its constructions are precise,
universal mathematics; its categories represent datatypes, programs, and
the languages that express them.

Active development is the Lean 4 formalisation under `geb-lean/`,
preceded by the Idris-2 implementation under `geb-idris/`. The Common
Lisp reference implementation and the Agda verification are original
efforts, retained for reference. This file indexes the project's
documentation.

<!-- START doctoc -->
<!-- END doctoc -->

## Lean formalisation (active)

- [`geb-lean/README.md`](geb-lean/README.md) — subproject overview and
  dependencies.
- [`geb-lean/docs/index.md`](geb-lean/docs/index.md) — index of the
  implemented mathematical content.

## Idris-2 implementation

- [`geb-idris/README.md`](geb-idris/README.md) — Geb as a circuit
  frontend.
- [`geb-idris/docs/index.md`](geb-idris/docs/index.md) — documentation
  index.
- [`geb-idris/EXAMPLES.md`](geb-idris/EXAMPLES.md) — Geb by example.

## Agda verification (original effort)

- [`geb-agda/README.md`](geb-agda/README.md) — formal verification of
  Geb's core-category properties.

## Common Lisp reference (original, mostly obsolete)

- [`docs/common-lisp/manual.md`](docs/common-lisp/manual.md) — the Geb
  manual generated from the Common Lisp implementation, retained for
  reference and superseded by the development above.
```

- [ ] **Step 2: Insert the table of contents and lint**

Run:

```bash
doctoc --github README.md
markdownlint-cli2 --config geb-lean/.markdownlint-cli2.jsonc --no-globs 'README.md'
```

Expected: doctoc reports the file updated; markdownlint reports
`0 error(s)`. (`doctoc --github` fills the `<!-- START doctoc -->` /
`<!-- END doctoc -->` block; the file has four `##` headings, so a TOC
is required.)

- [ ] **Step 3: Verify all index link targets exist**

Run:

```bash
for p in geb-lean/README.md geb-lean/docs/index.md \
         geb-idris/README.md geb-idris/docs/index.md geb-idris/EXAMPLES.md \
         geb-agda/README.md docs/common-lisp/manual.md; do
  test -e "$p" && echo "ok $p" || echo "MISSING $p"
done
```

Expected: every line begins with `ok`.

- [ ] **Step 4: Commit**

```bash
jj commit -m "docs: add hand-authored root README documentation index

Replace the former generated root README.md (relocated in an earlier
commit) with a short identity statement and a categorized index linking
to the Lean, Idris, Agda, and Common Lisp documentation."
jj bookmark set docs/readme-docs-revamp -r @-
```

## Task 8: Final verification

**Files:** none (verification only).

- [ ] **Step 1: Confirm regeneration never touches the new root README**

Run the generator once more and confirm the hand-authored
`README.md` is untouched and the tree stays clean:

```bash
cp README.md /tmp/index-README.md
timeout 600 ros run \
  -e '(asdf:load-asd (truename "geb.asd"))' \
  -e '(ql:quickload :geb :silent t)' \
  -e '(ql:quickload :geb/documentation :silent t)' \
  -e '(ql:quickload :mgl-pax/navigate :silent t)' \
  -e '(ql:quickload :mgl-pax/document :silent t)' \
  -e '(funcall (uiop:find-symbol* :build-docs :geb-docs/docs))' \
  -e '(format t "~%FINAL-BUILD-OK~%")' \
  -q 2>&1 | tail -3
diff /tmp/index-README.md README.md && echo "ROOT-README-UNTOUCHED"
jj status
```

Expected: `FINAL-BUILD-OK`, `ROOT-README-UNTOUCHED`, and `jj status`
reports no changes. This is the central guarantee: a documentation
rebuild leaves both the hand-authored root `README.md` and the committed
`manual.md` unchanged.

- [ ] **Step 2: Confirm the full branch shape**

Run:

```bash
jj log -r 'main..docs/readme-docs-revamp' --no-graph \
  -T 'description.first_line() ++ "\n"'
```

Expected: the spec commits followed by the seven task commits (relocate
manual, relocate sources, delete README, retarget generator, regenerate
manual, idris index, root README), each a single conceptual operation.

- [ ] **Step 3: Lint all authored markdown once more**

Run:

```bash
markdownlint-cli2 --config geb-lean/.markdownlint-cli2.jsonc --no-globs \
  'README.md' 'geb-idris/docs/index.md' \
  'docs/superpowers/specs/2026-05-28-readme-docs-revamp-design.md' \
  'docs/superpowers/plans/2026-05-28-readme-docs-revamp-plan.md'
```

Expected: `0 error(s)`.

- [ ] **Step 4: Hand off for user review before any push**

Present the branch (`jj log` and key diffs) to the user for line-by-line
review. Do not run `jj git push` until the user approves.

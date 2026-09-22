#!/usr/bin/env bash
# Refresh vendor/geb-mathlib from upstream and re-apply the back-port patch.
# Usage: scripts/refresh-geb-mathlib.sh [<source-rev>]   (default: main)
set -euo pipefail

REPO_URL="https://github.com/rokopt/geb-mathlib.git"
SRC_REV="${1:-main}"

# Modules dropped from the vendored copy, each with its submodules and
# every import of it. A module qualifies when it depends on a definition
# absent from the pinned toolchain's dependencies and no patch hunk can
# supply it. See docs/geb-mathlib-backport-notes.md § Module exclusion.
#
# Name the narrowest module that carries the dependency, so that a
# sibling added upstream later is ingested rather than silently dropped.
#
# A module importing an excluded module is excluded in turn, since the
# import deletion below would otherwise leave it referring to
# declarations it no longer imports. The one exception is a directory's
# index module, which carries nothing but imports and survives the
# deletion.
#
# Geb.Prototypes.Computability.TreeScanner, and under
# Geb.Prototypes.Computability.BitTree the modules Bound, Machine,
# Steps, BinaryMachine.{Bound,Machine}, Elias.{Bound,Machine}, and
# EliasBinary.Bound, and Geb.Prototypes.Computability.BitTreeScanner.Machine:
# import
# Cslib.Computability.Machines.Turing.MultiTape.{Deterministic,TapeLemmas},
# added to cslib after the pinned v4.29.0-rc6 revision.
#
# Geb.Prototypes.Computability.BitTreeScanner.Encoding: imports
# Cslib.Foundations.Data.PFunctor.Free, likewise added after the pin.
#
# Geb.Prototypes.Computability.MultiTape.{OutputString,Rename} and
# Geb.Prototypes.Computability.SizeBounded.Machine.{Exec,Program,Register}:
# import the MultiTape modules above and
# Cslib.Computability.Machines.Turing.MultiTape.Configuration, also
# added after the pin.
#
# Geb.Prototypes.Computability.Oitavem.Machine.SpaceTime: imports
# Cslib.Computability.Machines.Turing.MultiTape.ConfigBound, likewise
# added after the pin.
#
# Geb.Prototypes.Computability.Oitavem.Word imports
# BitTreeScanner.Encoding; every other Oitavem module imports Word,
# so Oitavem is excluded as a whole, and with it its importers
# BitStream.Oitavem, Typechecker.Oitavem, and RoseTree.Bits (whose
# importers Spine and Packed follow).
#
# The remaining entries import one of the above, directly or through
# a chain of such imports, or are imported only by such modules, which
# would leave them unreachable from the Geb umbrella
# (scripts/tests/test-lint-driver.sh reports these).
EXCLUDED_MODULES=(
  Geb.Prototypes.BitStream.Oitavem
  Geb.Prototypes.Computability.BitTree.BinaryMachine.Accounting
  Geb.Prototypes.Computability.BitTree.BinaryMachine.BitStep
  Geb.Prototypes.Computability.BitTree.BinaryMachine.Bound
  Geb.Prototypes.Computability.BitTree.BinaryMachine.Carry
  Geb.Prototypes.Computability.BitTree.BinaryMachine.Difference
  Geb.Prototypes.Computability.BitTree.BinaryMachine.Execution
  Geb.Prototypes.Computability.BitTree.BinaryMachine.Machine
  Geb.Prototypes.Computability.BitTree.BinaryMachine.Macro
  Geb.Prototypes.Computability.BitTree.BinaryMachine.Representation
  Geb.Prototypes.Computability.BitTree.BinaryMachine.Return
  Geb.Prototypes.Computability.BitTree.BinaryMachine.Simulation
  Geb.Prototypes.Computability.BitTree.BinaryMachine.Steps
  Geb.Prototypes.Computability.BitTree.Bound
  Geb.Prototypes.Computability.BitTree.Elias.Bound
  Geb.Prototypes.Computability.BitTree.Elias.Counter
  Geb.Prototypes.Computability.BitTree.Elias.Execution
  Geb.Prototypes.Computability.BitTree.Elias.Machine
  Geb.Prototypes.Computability.BitTree.Elias.MachineAccounting
  Geb.Prototypes.Computability.BitTree.Elias.MachineBit
  Geb.Prototypes.Computability.BitTree.Elias.MachineConfig
  Geb.Prototypes.Computability.BitTree.Elias.MachineCounter
  Geb.Prototypes.Computability.BitTree.Elias.MachineEmpty
  Geb.Prototypes.Computability.BitTree.Elias.MachineEnd
  Geb.Prototypes.Computability.BitTree.Elias.MachineHeader
  Geb.Prototypes.Computability.BitTree.Elias.MachineHeaderBound
  Geb.Prototypes.Computability.BitTree.Elias.MachineModel
  Geb.Prototypes.Computability.BitTree.Elias.MachineNormalize
  Geb.Prototypes.Computability.BitTree.Elias.MachinePayload
  Geb.Prototypes.Computability.BitTree.Elias.MachineRead
  Geb.Prototypes.Computability.BitTree.Elias.MachineSimpleBound
  Geb.Prototypes.Computability.BitTree.Elias.MachineSteps
  Geb.Prototypes.Computability.BitTree.Elias.Scanner
  Geb.Prototypes.Computability.BitTree.Elias.ScannerCorrect
  Geb.Prototypes.Computability.BitTree.Elias.ScannerHeader
  Geb.Prototypes.Computability.BitTree.EliasBinary.Account
  Geb.Prototypes.Computability.BitTree.EliasBinary.BitStep
  Geb.Prototypes.Computability.BitTree.EliasBinary.Bound
  Geb.Prototypes.Computability.BitTree.EliasBinary.Cost
  Geb.Prototypes.Computability.BitTree.EliasBinary.Execution
  Geb.Prototypes.Computability.BitTree.EliasBinary.Increment
  Geb.Prototypes.Computability.BitTree.EliasBinary.Layout
  Geb.Prototypes.Computability.BitTree.EliasBinary.LengthRead
  Geb.Prototypes.Computability.BitTree.EliasBinary.Machine
  Geb.Prototypes.Computability.BitTree.EliasBinary.Need
  Geb.Prototypes.Computability.BitTree.EliasBinary.PassOne
  Geb.Prototypes.Computability.BitTree.EliasBinary.Payload
  Geb.Prototypes.Computability.BitTree.EliasBinary.Represent
  Geb.Prototypes.Computability.BitTree.EliasBinary.Simple
  Geb.Prototypes.Computability.BitTree.EliasBinary.SizeRead
  Geb.Prototypes.Computability.BitTree.EliasBinary.Steps
  Geb.Prototypes.Computability.BitTree.EliasBinary.Zeros
  Geb.Prototypes.Computability.BitTree.Machine
  Geb.Prototypes.Computability.BitTree.Steps
  Geb.Prototypes.Computability.BitTreeScanner
  Geb.Prototypes.Computability.Kristiansen.MachineBound
  Geb.Prototypes.Computability.Mazzanti.BitTree
  Geb.Prototypes.Computability.Mazzanti.Bound
  Geb.Prototypes.Computability.Mazzanti.Growth
  Geb.Prototypes.Computability.Mazzanti.Words
  Geb.Prototypes.Computability.MultiTape
  Geb.Prototypes.Computability.Oitavem
  Geb.Prototypes.Computability.SizeBounded.Logspace.EliasTree
  Geb.Prototypes.Computability.SizeBounded.Logspace.Machine
  Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.BitFold
  Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.ChildExpr
  Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Children
  Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Events
  Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.ExprBase
  Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Machine
  Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.NodeExpr
  Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Nodes
  Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.NumArith
  Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.NumScanExpr
  Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.NumSum
  Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Recognize
  Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.RecognizeExpr
  Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.SigCheck
  Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.SigEdge
  Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.SigLabel
  Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.SigMachine
  Geb.Prototypes.Computability.SizeBounded.Machine
  Geb.Prototypes.Computability.SizeBounded.MachineBound
  Geb.Prototypes.Computability.SizeBounded.WordMachine
  Geb.Prototypes.Computability.TreeScanner
  Geb.Prototypes.RoseTree.Bits
  Geb.Prototypes.RoseTree.Packed
  Geb.Prototypes.RoseTree.Spine
  Geb.Prototypes.Typechecker.Oitavem
)
ROOT="$(cd "$(dirname "$0")/.." && pwd)"   # geb-lean package root
VENDOR="$ROOT/vendor/geb-mathlib"
PATCH="$ROOT/scripts/geb-mathlib-backport.patch"

# Fail immediately if the back-port patch is missing.
[ -f "$PATCH" ] || { echo "error: back-port patch not found: $PATCH" >&2; exit 1; }

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
git clone --quiet "$REPO_URL" "$TMP/gm"
git -C "$TMP/gm" checkout --quiet "$SRC_REV"
# A content checksum, not a commit hash: the commit that last touched
# the patch is unavailable in a shallow CI checkout and cannot name
# itself when the patch and PROVENANCE.md change in the same commit.
SRC_SHA="$(git -C "$TMP/gm" rev-parse HEAD)"
PATCH_SHA256="$(sha256sum "$PATCH" | cut -d' ' -f1)"
# One sub-list item per entry; a single line would be unreadable.
EXCLUDED_RENDERED="$(printf '\n  - %s' "${EXCLUDED_MODULES[@]}")"

# Complete overwrite of the Geb namespace (no orphaned files).
rm -f "$VENDOR/Geb.lean"; rm -rf "$VENDOR/Geb"
cp "$TMP/gm/Geb.lean" "$VENDOR/Geb.lean"
cp -R "$TMP/gm/Geb" "$VENDOR/Geb"
cp "$TMP/gm/LICENSE" "$VENDOR/LICENSE"

cat > "$VENDOR/PROVENANCE.md" <<EOF
# Vendored geb-mathlib provenance

- Source: $REPO_URL
- Source commit: $SRC_SHA
- Back-port patch: scripts/geb-mathlib-backport.patch (sha256 $PATCH_SHA256)
- Excluded modules, each dropped along with its submodules and every import of it (see scripts/refresh-geb-mathlib.sh):$EXCLUDED_RENDERED
- \`GebMeta\` is not vendored: every import of it is dropped, each \`{cite}\` docstring role it supplies is rewritten to its escaped bracketed key, and each \`{name}\` role naming one of its declarations is rewritten to \`{lit}\`; see scripts/refresh-geb-mathlib.sh.
- The files under \`Geb/\` are an unmodified mirror of the source commit except where the back-port patch changes them and where the exclusion above removes them; modified files carry a change notice in their header comment.
EOF

# Apply the back-port patch; a rejection is a hard, reportable failure.
# git apply resolves paths from the git repository root, not from a
# subdirectory; use --directory so the patch paths (vendor/geb-mathlib/...)
# resolve correctly when geb-lean is a subdirectory of a monorepo.
GIT_ROOT="$(git -C "$ROOT" rev-parse --show-toplevel)"
REL="$(realpath --relative-to="$GIT_ROOT" "$ROOT")"
( cd "$GIT_ROOT" && git apply -p1 --directory="$REL" "$PATCH" )

# Drop excluded modules after patching, so every hunk still anchors
# against the pristine upstream text it was generated from.
for mod in "${EXCLUDED_MODULES[@]}"; do
  rm -f "$VENDOR/${mod//.//}.lean"
  rm -rf "$VENDOR/${mod//.//}"
  # An import of an excluded module or of any of its submodules would
  # leave the surviving tree with a bad import.
  find "$VENDOR" -name '*.lean' -exec \
    sed -i -E "/^(public )?import ${mod}(\.|\$)/d" {} +
done

# GebMeta is not vendored (its env_linter would mis-audit geb-lean). It
# supplies the `{cite}` docstring role, which upstream's literate
# modules use under `doc.verso`; the pinned toolchain supports every
# other role such a module writes. Drop each import of GebMeta, in any
# of the module system's four forms; rewrite each `{cite}` span to
# the escaped bracketed key, `\[Key\]`, the `doc.verso` spelling of
# mathlib's bare `[Key]` citation form; and rewrite each `{name}` span
# naming a GebMeta declaration to a `{lit}` span, since `{name}`
# resolves its constant and the constant is absent. See
# docs/geb-mathlib-backport-notes.md § 1.
find "$VENDOR" -name '*.lean' -exec sed -i -E \
  -e '/^(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+GebMeta([[:space:]]|$)/d' \
  -e 's/[{]cite[}]`([^`]*)`/\\[\1\\]/g' \
  -e 's/[{]name[}]`(GebMeta\.[^`]*)`/{lit}`\1`/g' {} +

# A refresh that changes no vendored content (an upstream revision
# touching none of the mirrored files) leaves at most PROVENANCE.md
# modified. Restore it in that case so the tree is byte-clean and the
# CI workflow's create-pull-request step opens no pull request.
if ! git -C "$GIT_ROOT" status --porcelain -- "$REL/vendor/geb-mathlib" \
    | grep -qv 'PROVENANCE\.md$'; then
  git -C "$GIT_ROOT" checkout -- "$REL/vendor/geb-mathlib/PROVENANCE.md"
  echo "No vendored content changed; refresh is a no-op."
else
  echo "Refreshed vendor/geb-mathlib to $SRC_SHA and applied back-port patch."
fi

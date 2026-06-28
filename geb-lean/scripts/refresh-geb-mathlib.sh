#!/usr/bin/env bash
# Refresh vendor/geb-mathlib from upstream and re-apply the back-port patch.
# Usage: scripts/refresh-geb-mathlib.sh [<source-rev>]   (default: main)
set -euo pipefail

REPO_URL="https://github.com/rokopt/geb-mathlib.git"
SRC_REV="${1:-main}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"   # geb-lean package root
VENDOR="$ROOT/vendor/geb-mathlib"
PATCH="$ROOT/scripts/geb-mathlib-backport.patch"

# Fail immediately if the back-port patch is missing.
[ -f "$PATCH" ] || { echo "error: back-port patch not found: $PATCH" >&2; exit 1; }

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
git clone --quiet "$REPO_URL" "$TMP/gm"
git -C "$TMP/gm" checkout --quiet "$SRC_REV"
SRC_SHA="$(git -C "$TMP/gm" rev-parse HEAD)"
PATCH_SHA="$(git -C "$ROOT" log -1 --format=%H -- "$PATCH" 2>/dev/null || echo unknown)"

# Complete overwrite of the Geb namespace (no orphaned files).
rm -f "$VENDOR/Geb.lean"; rm -rf "$VENDOR/Geb"
cp "$TMP/gm/Geb.lean" "$VENDOR/Geb.lean"
cp -R "$TMP/gm/Geb" "$VENDOR/Geb"
cp "$TMP/gm/LICENSE" "$VENDOR/LICENSE"

cat > "$VENDOR/PROVENANCE.md" <<EOF
# Vendored geb-mathlib provenance

- Source: $REPO_URL
- Source commit: $SRC_SHA
- Back-port patch: scripts/geb-mathlib-backport.patch (commit $PATCH_SHA)
- The files under \`Geb/\` are an unmodified mirror of the source commit except where the back-port patch changes them; modified files carry a change notice in their header comment.
EOF

# Apply the back-port patch; a rejection is a hard, reportable failure.
# git apply resolves paths from the git repository root, not from a
# subdirectory; use --directory so the patch paths (vendor/geb-mathlib/...)
# resolve correctly when geb-lean is a subdirectory of a monorepo.
GIT_ROOT="$(git -C "$ROOT" rev-parse --show-toplevel)"
REL="$(realpath --relative-to="$GIT_ROOT" "$ROOT")"
( cd "$GIT_ROOT" && git apply -p1 --directory="$REL" "$PATCH" )
echo "Refreshed vendor/geb-mathlib to $SRC_SHA and applied back-port patch."

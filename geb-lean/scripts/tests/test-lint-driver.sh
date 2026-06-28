#!/usr/bin/env bash
#
# scripts/tests/test-lint-driver.sh
#
# Guards the lint-coverage invariant that bounds runLinter memory
# when linting the vendored geb-mathlib tree.
#
# The geb-mathlib refresh workflow lints the vendored library by
# invoking batteries/runLinter on the single root module `Geb`.
# runLinter loads one flat environment whose declaration set
# (getDeclsInPackage) covers every module the `Geb` umbrella
# transitively imports. Passing each `Geb.*` module as a separate
# argument instead loads one environment per module — each
# re-importing the full mathlib closure — so peak memory scales
# with module count and exhausts a standard 16 GiB CI runner.
#
# Two properties are checked:
#   1. Invocation form: the refresh workflow lints root module
#      `Geb` (`lake lint -- Geb`) and does not enumerate the
#      vendored modules into the lint arguments.
#   2. Coverage completeness: every vendored `Geb.*` source module
#      is transitively imported by the `Geb` umbrella, so linting
#      the root module reaches every declaration the per-module
#      form would have. A module orphaned from the umbrella would
#      escape the linter entirely under the root-module invocation.
#
# Exit 0 if both hold; non-zero otherwise.

set -uo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
failed=0

vroot="vendor/geb-mathlib"
workflow="../.github/workflows/geb-mathlib-refresh.yml"

# --- 1. Invocation form -------------------------------------------------
# The refresh workflow lives in the parent monorepo's .github tree.
if [[ ! -f "$workflow" ]]; then
  echo "NOTE: $workflow not found; skipping invocation-form check." >&2
else
  if ! grep -qE '^\s*lake lint -- Geb\s*$' "$workflow"; then
    echo "FAIL: refresh workflow does not lint root module Geb" >&2
    echo "  expected a 'lake lint -- Geb' line in $workflow" >&2
    failed=1
  fi
  if grep -qE 'lake lint.*VMODS' "$workflow"; then
    echo "FAIL: refresh workflow lints enumerated modules (high memory)" >&2
    echo "  found a per-module 'lake lint -- \$VMODS' form in $workflow" >&2
    failed=1
  fi
fi

# --- 2. Coverage completeness (no module orphaned from the umbrella) -----
# Module name to file path: dots map to slashes; the root module
# `Geb` lives at `$vroot/Geb.lean`, the rest under `$vroot/Geb/`.
mod_to_file() { echo "$vroot/${1//.//}.lean"; }

all_mods="$( { echo Geb; find "$vroot/Geb" -name '*.lean' \
  | sed -E "s,^$vroot/,,; s,/,.,g; s,\.lean\$,,"; } | sort -u )"

# Transitive closure of `import Geb.*` reachable from the `Geb` root.
reachable="Geb"
frontier="Geb"
while [[ -n "$frontier" ]]; do
  next=""
  for m in $frontier; do
    f="$(mod_to_file "$m")"
    [[ -f "$f" ]] || continue
    imps="$(grep -oE '^(public )?import Geb(\.[A-Za-z0-9_]+)+' "$f" \
      | sed -E 's/^(public )?import //')"
    for i in $imps; do
      if ! grep -qxF "$i" <<<"$reachable"; then
        reachable="$reachable"$'\n'"$i"
        next="$next $i"
      fi
    done
  done
  frontier="$next"
done
reachable="$(sort -u <<<"$reachable")"

orphans="$(comm -23 <(echo "$all_mods") <(echo "$reachable"))"
if [[ -n "$orphans" ]]; then
  echo "FAIL: vendored modules not reachable from the 'Geb' umbrella" >&2
  echo "  (these would escape 'lake lint -- Geb'):" >&2
  echo "$orphans" | sed 's/^/  /' >&2
  failed=1
fi

if [[ "$failed" -ne 0 ]]; then
  echo "test-lint-driver: FAIL" >&2
  exit 1
fi
echo "test-lint-driver: ok"
exit 0

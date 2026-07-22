#!/usr/bin/env bash
#
# scripts/tests/test-lint-driver.sh
#
# Guards the lint-coverage invariant that bounds runLinter memory
# when linting a library via its root module.
#
# batteries/runLinter loads one flat environment whose declaration
# set (getDeclsInPackage) covers every module the root module
# transitively imports. Passing each module as a separate argument
# instead loads one environment per module — each re-importing the
# full mathlib closure — so peak memory scales with module count
# and exhausts a standard 16 GiB CI runner. Each library below is
# therefore linted via its root module in its own workflow.
#
# Two properties are checked per library:
#   1. Invocation form: the library's workflow lints its root
#      module (`lake lint -- <library>`) and does not enumerate
#      its modules into the lint arguments.
#   2. Coverage completeness: every source module under the
#      library's root is transitively imported by the root module,
#      so linting the root reaches every declaration the
#      per-module form would have. A module orphaned from the
#      umbrella would escape the linter entirely under the
#      root-module invocation.
#
# Exit 0 if both hold for every library below; non-zero otherwise.

set -uo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
failed=0

# library | source root | workflow file
libs=(
  "Geb|vendor/geb-mathlib|../.github/workflows/geb-mathlib-refresh.yml"
  "GebLeanDocs|.|../.github/workflows/lean_action_ci.yml"
)

for entry in "${libs[@]}"; do
  IFS='|' read -r lib vroot workflow <<<"$entry"

  # --- 1. Invocation form -------------------------------------------------
  # Workflow files live in the parent monorepo's .github tree.
  if [[ ! -f "$workflow" ]]; then
    echo "NOTE: $workflow not found; skipping invocation-form check for $lib." >&2
  else
    if ! grep -qE "^\s*lake lint -- $lib\s*\$" "$workflow"; then
      echo "FAIL: workflow does not lint root module $lib" >&2
      echo "  expected a 'lake lint -- $lib' line in $workflow" >&2
      failed=1
    fi
    if grep -qE 'lake lint.*VMODS' "$workflow"; then
      echo "FAIL: workflow lints enumerated modules (high memory)" >&2
      echo "  found a per-module 'lake lint -- \$VMODS' form in $workflow" >&2
      failed=1
    fi
  fi

  # --- 2. Coverage completeness (no module orphaned from the umbrella) ---
  # Module name to file path: dots map to slashes; the root module
  # `$lib` lives at `$vroot/$lib.lean`, the rest under `$vroot/$lib/`.
  mod_to_file() { echo "$vroot/${1//.//}.lean"; }

  all_mods="$( { echo "$lib"; find "$vroot/$lib" -name '*.lean' \
    | sed -E "s,^$vroot/,,; s,/,.,g; s,\.lean\$,,"; } | sort -u )"

  # Transitive closure of `import <lib>.*` reachable from the root.
  reachable="$lib"
  frontier="$lib"
  while [[ -n "$frontier" ]]; do
    next=""
    for m in $frontier; do
      f="$(mod_to_file "$m")"
      [[ -f "$f" ]] || continue
      imps="$(grep -oE "^(public )?import $lib(\.[A-Za-z0-9_]+)+" "$f" \
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
    echo "FAIL: $lib modules not reachable from the '$lib' umbrella" >&2
    echo "  (these would escape 'lake lint -- $lib'):" >&2
    echo "$orphans" | sed 's/^/  /' >&2
    failed=1
  fi
done

if [[ "$failed" -ne 0 ]]; then
  echo "test-lint-driver: FAIL" >&2
  exit 1
fi
echo "test-lint-driver: ok"
exit 0

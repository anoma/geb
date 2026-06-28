#!/usr/bin/env bash
#
# scripts/tests/test-axiom-linter.sh
#
# Smoke test for the GebLeanMeta.detectNonstandardAxiom env_linter.
# Stages throwaway fixtures in a temp directory: a violating one (a
# theorem proved via a custom axiom) that the linter must reject, a
# clean one it must accept, and a Classical.choice one it must accept
# (geb-lean permits Classical.choice project-wide). Nothing
# axiom-violating is committed.
#
# The fixtures live outside the package, so the linter is run on them
# with `lake env lean`; they set no lakefile options, so the spurious
# diagnostics `lake env lean` can otherwise produce do not arise.
#
# Exit 0 if all scenarios behave; non-zero otherwise.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
failed=0

cat > "$tmp/Bad.lean" <<'EOF'
import GebLeanMeta
import Batteries.Tactic.Lint
axiom badAx : (1 : Nat) = 2
theorem usesBad : (1 : Nat) = 2 := badAx
#lint only detectNonstandardAxiom
EOF

cat > "$tmp/Good.lean" <<'EOF'
import GebLeanMeta
import Batteries.Tactic.Lint
theorem fine : True := True.intro
#lint only detectNonstandardAxiom
EOF

cat > "$tmp/Choice.lean" <<'EOF'
import GebLeanMeta
import Batteries.Tactic.Lint
theorem usesChoice : True :=
  (Classical.em True).elim (fun _ => trivial) (fun _ => trivial)
#lint only detectNonstandardAxiom
EOF

out_bad="$(lake env lean "$tmp/Bad.lean" 2>&1)"
rc_bad=$?
if [[ "$rc_bad" -eq 0 ]]; then
  echo "FAIL: linter accepted a declaration using a non-standard axiom" >&2
  echo "  output: $out_bad" >&2
  failed=1
fi
if ! grep -qF 'badAx' <<<"$out_bad"; then
  echo "FAIL: violation output did not name the offending axiom 'badAx'" >&2
  echo "  output: $out_bad" >&2
  failed=1
fi

out_good="$(lake env lean "$tmp/Good.lean" 2>&1)"
rc_good=$?
if [[ "$rc_good" -ne 0 ]]; then
  echo "FAIL: linter rejected clean code" >&2
  echo "  output: $out_good" >&2
  failed=1
fi

out_choice="$(lake env lean "$tmp/Choice.lean" 2>&1)"
rc_choice=$?
if [[ "$rc_choice" -ne 0 ]]; then
  echo "FAIL: linter rejected Classical.choice (permitted project-wide)" >&2
  echo "  output: $out_choice" >&2
  failed=1
fi

if [[ "$failed" -ne 0 ]]; then
  echo "test-axiom-linter: FAIL" >&2
  exit 1
fi
echo "test-axiom-linter: ok"
exit 0

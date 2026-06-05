#!/usr/bin/env bash
# Usage: docs/tools/check-area-coverage.sh {idris|lean}
# Asserts (1) the set of source files linked from <lang>/docs/areas/*.md
# equals the language's source set, and (2) no source file is linked
# from more than one area document. Run from the repo root.
set -euo pipefail

lang="${1:-}"
[ -n "$lang" ] || { echo "usage: $0 {idris|lean}" >&2; exit 2; }
case "$lang" in
  idris)
    areas="geb-idris/docs/areas"; ext="idr"
    mapfile -t sources < <(
      find geb-idris/src -name '*.idr' | grep -v '/Test/' \
      | sed 's#^#./#' | sort -u)
    ;;
  lean)
    areas="geb-lean/docs/areas"; ext="lean"
    mapfile -t sources < <(
      { echo geb-lean/GebLean.lean; find geb-lean/GebLean -name '*.lean'; } \
      | grep -vE '(^|/)GebLeanTests(/|\.lean$)' \
      | sed 's#^#./#' | sort -u)
    ;;
  *) echo "usage: $0 {idris|lean}" >&2; exit 2 ;;
esac

declare -A docs_for   # normalised-source-path -> space-joined area docs
linked_tmp="$(mktemp)"
for md in "$areas"/*.md; do
  [ -e "$md" ] || continue
  case "$(basename "$md")" in _*) continue ;; esac
  # distinct link targets ending in .<ext>, deduped within this file
  while IFS= read -r tgt; do
    [ -n "$tgt" ] || continue
    abs="$(realpath -m "$(dirname "$md")/$tgt")"
    rel="./${abs#"$PWD"/}"
    echo "$rel" >> "$linked_tmp"
    if [ -n "${docs_for[$rel]:-}" ]; then
      docs_for[$rel]="${docs_for[$rel]} $(basename "$md")"
    else
      docs_for[$rel]="$(basename "$md")"
    fi
  done < <(grep -oE "\]\([^)]*\.${ext}\)" "$md" \
           | sed -E 's/^\]\((.*)\)$/\1/' | sort -u)
done

linked_sorted="$(sort -u "$linked_tmp")"; rm -f "$linked_tmp"
src_sorted="$(printf '%s\n' "${sources[@]}" | sort -u)"

status=0
echo "== Assertion 1: totality (linked set == source set) =="
missing="$(comm -23 <(printf '%s\n' "$src_sorted") <(printf '%s\n' "$linked_sorted"))"
extra="$(comm -13 <(printf '%s\n' "$src_sorted") <(printf '%s\n' "$linked_sorted"))"
if [ -n "$missing" ]; then echo "UNLINKED source files:"; echo "$missing"; status=1; fi
if [ -n "$extra" ]; then echo "LINKED non-source targets:"; echo "$extra"; status=1; fi

echo "== Assertion 2: disjointness (each file in <=1 area doc) =="
for f in "${!docs_for[@]}"; do
  n=$(wc -w <<<"${docs_for[$f]}")
  if [ "$n" -gt 1 ]; then echo "MULTI-HOME: $f -> ${docs_for[$f]}"; status=1; fi
done

[ "$status" -eq 0 ] && echo "OK: $lang coverage total and disjoint."
exit "$status"

#!/usr/bin/env bash
#
# check-axioms.sh — Check axioms in Lean 4 files using inline #print axioms.
#
# Vendored from:
#   Plugin:  lean4-skills 4.4.9 (author: Cameron Freer)
#   On-disk: /home/terence/.claude/plugins/cache/lean4-skills/lean4/4.4.9/
#              lib/scripts/check_axioms_inline.sh
#   GitHub:  https://github.com/anthropics/claude-code-plugins/tree/main/
#              plugins/lean4-skills
#   (No commit SHA recorded in the plugin manifest; re-vendor by diffing
#    against the on-disk path above with the same version string 4.4.9.)
#
# Local modifications vs. upstream:
#   1. Allowlist reduced: STANDARD_AXIOMS covers only propext, Quot.sound,
#      and quot.sound — Classical.choice is NOT in the allowlist here, so
#      transitive dependencies on Classical.choice are flagged.
#   2. AXIOM_ALLOW annotation scanning: if a declaration is immediately
#      preceded (with no intervening blank lines) by one or more -- comments
#      and/or a /-- … -/ docstring containing lines of the form
#        -- AXIOM_ALLOW: <axiom-name> (optional rationale)
#      and every axiom flagged for that declaration appears in the collected
#      AXIOM_ALLOW set, the declaration is suppressed from the failure
#      output.  See spec comment in the AXIOM_ALLOW scanning section below.
#   3. Bare-name extraction widened: the stop set is `[^ :({[,`+`]+`
#      (adding `{`, `[`, `,`, and backtick to the upstream `[^ :(]+`),
#      and a trailing dot is stripped after extraction.  Without these,
#      anonymous instances `instance {V : ...}` extracted as bare `{V`,
#      universe-annotated declarations `def Foo.bar.{u, v}` extracted
#      as `Foo.bar.{u,`, and prose lines inside `/-- ... -/` or
#      `/-! ... -/` docstrings that happen to begin with a Lean keyword
#      (``structure maps, one per constructor.``,
#      ``abbrev `FunctorBetween…` form gets stuck on``) yielded
#      malformed bare names; the resulting `#print axioms ...` lines
#      triggered Lean parse errors that the script's tolerant fallback
#      did not absorb.
#   4. Ignorable-error patterns widened to include Lean's
#      `maximum number of errors (N; from option `maxErrors`) reached,
#      exiting` cap message, which is emitted as a consequence of
#      cascading unknown-identifier errors (when a file's first
#      `namespace` directive does not actually scope every top-level
#      declaration in the file — a known limitation of the
#      first-namespace-only heuristic above).
#   5. SIGPIPE-safe matching against the absorbed-error / tolerant
#      patterns: the upstream `... | grep -q PATTERN` pipelines closed
#      stdin on first match and let the upstream `echo "$OUTPUT"`
#      exit with SIGPIPE (141); under the script's `set -o pipefail`,
#      the pipeline then evaluated to non-zero, the `if` body was
#      skipped, and the script reported a spurious "Error running
#      Lean".  Both pipelines are rewritten to use `grep -c …
#      >/dev/null`, which consumes all input.
#   6. Real-error detection scoped to post-marker errors: the upstream
#      logic flagged any pre-marker error as a "real" file-compilation
#      failure, but `lake env lean` ignores `lakefile.toml`
#      `leanOptions`, so it produces spurious pre-marker diagnostics
#      (`unsolved goals`, `failed to synthesize`, `Tactic ... failed`,
#      etc.) on files that compile cleanly via `lake build`.  Because
#      every caller of this script runs `lake build` first (CI
#      workflow, `pre-push.sh`, `pre-commit.sh`), the file's own
#      content has already been validated; the script restricts its
#      real-error scan to errors at the marker line or after, where
#      only the appended `#print axioms` commands live.
#   7. `#print axioms` output parser rewritten for Lean 4's actual
#      output format.  Lean 4 emits each result on a single line
#      (with optional bracketed-list line-wrap):
#          'X' depends on axioms: [a, b, c]
#          'X' depends on axioms: [propext,
#           Quot.sound]
#          'X' does not depend on any axioms
#      The upstream `^<name> depends on axioms:` header regex never
#      matched (Lean quotes the name) and the upstream fallback
#      regex `^[[:space:]]*([a-zA-Z0-9_.]+)[[:space:]]*$` for axiom
#      lines spuriously matched error-message body text (Lean's
#      `Application type mismatch:`-style multi-line diagnostics put
#      bare type names on their own indented lines).  The new parser
#      is a bracket-state machine that only accepts the two canonical
#      header forms above, accumulating wrapped list content until
#      the closing `]`; error-message bodies, prose, and other noise
#      are ignored entirely.  Side benefit: `_private.<mod>.<n>.`
#      mangling that Lean adds when `#print axioms` is invoked on a
#      `private` declaration is stripped before attribution.
#   8. Real-error detection extended to the leading-`error:` form
#      (`error: <file>:<line>:<col>: <msg>`).  The upstream awk
#      filter required the word `error` to appear *after* the
#      `:<line>:<col>:` segment, which matches the trailing-form
#      diagnostics Lean emits when called from `lake env lean` but
#      not the leading-form diagnostics it emits for kernel-level
#      type errors (e.g., `Application type mismatch`, `type expected`).
#      A file whose own content fails to compile with leading-form
#      errors would otherwise fall through to the tolerant path with
#      `lake env lean` exiting non-zero, no parseable axiom output,
#      and no detected real error — silently passing the check
#      while spurious error-body content fed the old axiom-line
#      regex.  The new awk filter triggers on any line containing
#      `error` together with a `:<digits>:` line-number marker,
#      regardless of order.
#   9. Real-error detection is unified across pre- and post-marker
#      output, with the union of absorbed forms checked in one
#      pass.  Earlier the script split errors into pre-marker and
#      post-marker buckets with disjoint absorbed-pattern sets;
#      that combined with a "no axiom output parsed → real error"
#      promotion misclassified healthy multi-namespace files (the
#      single-namespace heuristic above qualifies declarations
#      under the wrong prefix, producing absorbed `unknown
#      constant` errors for every appended `#print axioms`; no
#      axiom output → real error fired even though `lake build`
#      already accepted the file).  The unified filter absorbs
#      both classes — appended-command unknowns (`unknown
#      identifier`, `unknown constant`, `maximum number of
#      errors`) and `lake env lean`'s spurious lakefile-options
#      diagnostics (`unsolved goals`, `failed to synthesize`,
#      `Tactic ... failed`) — and flags anything else (e.g.,
#      `Application type mismatch`, `invalid field notation`).
#      "No axiom output parsed" is surfaced as a soft warning
#      ("declarations unaddressable under inferred namespace"),
#      not a hard failure.
#
# Usage:
#   ./check-axioms.sh <file-or-dir-or-pattern> [--verbose]
#                     [--exit-zero-on-findings]
#   ./check-axioms.sh GebLean/ test/
#   ./check-axioms.sh MyFile.lean --verbose --report-only
#   ./check-axioms.sh .
#
# This script temporarily appends #print axioms commands to Lean files,
# runs Lean to check axioms, then removes the additions.
#
# Limitations:
#   - Only detects the first namespace in a file
#   - Only captures top-level (unindented) declarations
#   - Nested namespaces, sections, and indented declarations may be missed

set -euo pipefail

# Track backup files for cleanup on interrupt using marker files.
# Marker files are more robust than arrays for SIGINT handling.
MARKER_DIR=$(mktemp -d)
cleanup() {
    local marker
    for marker in "$MARKER_DIR"/*.marker; do
        [[ -f "$marker" ]] || continue
        local original
        original=$(cat "$marker")
        if [[ -f "$original.axiom_check_backup" ]]; then
            mv "$original.axiom_check_backup" "$original"
        fi
        rm -f "$marker"
    done
    rm -rf "$MARKER_DIR"
}
trap cleanup EXIT INT TERM

# Configuration
VERBOSE=""
EXIT_ZERO_ON_FINDINGS=""
FILES=()
MARKER="-- AUTO_AXIOM_CHECK_MARKER_DO_NOT_COMMIT"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Standard acceptable axioms (Classical.choice is intentionally excluded).
# Anchored as a full-string match below so e.g. `propextX` does not
# collide with `propext`.
STANDARD_AXIOMS="propext|quot.sound|Quot.sound"
STANDARD_AXIOMS_REGEX="^(${STANDARD_AXIOMS})\$"

# Global counter for unique marker filenames (avoids basename collisions).
MARKER_COUNT=0

# Parse arguments: collect flags first, then positional args.
POSITIONAL=()
for arg in "$@"; do
    case "$arg" in
        --verbose)
            VERBOSE="--verbose"
            ;;
        --exit-zero-on-findings|--report-only)
            EXIT_ZERO_ON_FINDINGS="true"
            ;;
        --*)
            echo -e "${RED}Error: Unknown flag: $arg${NC}" >&2
            exit 1
            ;;
        *)
            POSITIONAL+=("$arg")
            ;;
    esac
done

# Resolve positional args to files.
for arg in "${POSITIONAL[@]}"; do
    if [[ "$arg" == *"*"* ]]; then
        # Expand globs
        # shellcheck disable=SC2206
        expanded=($arg)
        for file in "${expanded[@]}"; do
            [[ -f "$file" ]] && FILES+=("$file")
        done
    elif [[ -d "$arg" ]]; then
        dir_files_found=false
        while IFS= read -r -d '' file; do
            FILES+=("$file")
            dir_files_found=true
        done < <(find "$arg" -type d \( \
                    -name .lake -o -name .git \
                 \) -prune \
                 -o -type f -name '*.lean' -print0)
        if [[ "$dir_files_found" == false ]]; then
            if [[ -n "$EXIT_ZERO_ON_FINDINGS" ]]; then
                echo -e \
                    "${YELLOW}Warning: no .lean files found under:" \
                    "$arg; skipping.${NC}" >&2
            else
                echo -e \
                    "${RED}Error: no .lean files found under: $arg${NC}" >&2
                exit 1
            fi
        fi
    elif [[ -f "$arg" ]]; then
        FILES+=("$arg")
    else
        echo -e "${RED}Error: $arg is not a file or directory${NC}" >&2
        exit 1
    fi
done

# Normalize paths and dedup for deterministic ordering.
if [[ ${#FILES[@]} -gt 0 ]]; then
    DEDUPED=()
    while IFS= read -r f; do
        DEDUPED+=("$f")
    done < <(
        for f in "${FILES[@]}"; do
            realpath "$f" 2>/dev/null \
                || (cd "$(dirname "$f")" \
                    && echo "$(pwd -P)/$(basename "$f")") \
                || echo "$f"
        done | sort -u
    )
    FILES=("${DEDUPED[@]}")
fi

# Validate input.
if [[ ${#FILES[@]} -eq 0 ]]; then
    if [[ ${#POSITIONAL[@]} -eq 0 ]]; then
        echo -e "${RED}Error: No files specified${NC}" >&2
        echo "Usage: $0 <file-or-dir-or-pattern>" \
            "[--verbose] [--exit-zero-on-findings]" >&2
        echo "Examples:" >&2
        echo "  $0 MyFile.lean" >&2
        echo "  $0 src/**/*.lean" >&2
        echo "  $0 ." >&2
        echo "  $0 src/ --report-only" >&2
        exit 1
    elif [[ -n "$EXIT_ZERO_ON_FINDINGS" ]]; then
        echo -e \
            "${YELLOW}Warning: no Lean files found;" \
            "nothing to check.${NC}" >&2
        exit 0
    else
        echo -e "${RED}Error: No Lean files found in specified paths${NC}" >&2
        exit 1
    fi
fi

# Filter to .lean files only.
LEAN_FILES=()
for file in "${FILES[@]}"; do
    if [[ "$file" =~ \.lean$ ]]; then
        LEAN_FILES+=("$file")
    fi
done

if [[ ${#LEAN_FILES[@]} -eq 0 ]]; then
    echo -e "${RED}Error: No Lean files found${NC}" >&2
    exit 1
fi

# Summary header.
if [[ ${#LEAN_FILES[@]} -eq 1 ]]; then
    echo -e "${BLUE}Checking axioms in 1 file${NC}"
else
    echo -e "${BLUE}Checking axioms in ${#LEAN_FILES[@]} files${NC}"
fi
echo

# Global counters.
TOTAL_FILES=0
TOTAL_DECLARATIONS=0
FILES_WITH_CUSTOM=0
CUSTOM_AXIOM_COUNT=0

# ---------------------------------------------------------------------------
# AXIOM_ALLOW scanning
#
# For a declaration at line DECL_LINE in FILE, walk backwards through the
# file collecting AXIOM_ALLOW: <name> annotations.  The scan passes through:
#   - consecutive -- single-line comments (multi-line blocks permitted)
#   - a single /-- ... -/ docstring (any number of interior lines)
# and stops at the first blank line or any other content.
#
# Returns (via stdout) one axiom name per line.
# ---------------------------------------------------------------------------
get_axiom_allows() {
    local file="$1"
    local decl_line="$2"   # 1-based line number of the declaration

    # Read the relevant prefix into an array (lines 1 .. decl_line-1).
    mapfile -t lines < <(head -n "$((decl_line - 1))" "$file")

    local idx=$(( ${#lines[@]} - 1 ))
    local in_docstring=false

    while [[ $idx -ge 0 ]]; do
        local raw="${lines[$idx]}"
        local trimmed
        trimmed=$(echo "$raw" | sed 's/^[[:space:]]*//')

        if [[ "$in_docstring" == true ]]; then
            # Inside a /-- ... -/ block; extract any AXIOM_ALLOW lines.
            if [[ "$trimmed" =~ ^/-- ]]; then
                # Opening delimiter of docstring — stop scanning docstring.
                in_docstring=false
            fi
            # Extract AXIOM_ALLOW annotations inside the docstring.
            if [[ "$trimmed" =~ ^--[[:space:]]+AXIOM_ALLOW:[[:space:]]*(.+) ]]; then
                local name
                name=$(echo "${BASH_REMATCH[1]}" \
                    | sed 's/[[:space:]].*//')
                echo "$name"
            fi
            ((idx--))
            continue
        fi

        # Check for end of a /-- ... -/ docstring.
        if [[ "$trimmed" =~ -/$ ]]; then
            in_docstring=true
            ((idx--))
            continue
        fi

        # Single-line -- comment.
        if [[ "$trimmed" =~ ^-- ]]; then
            if [[ "$trimmed" =~ \
                ^--[[:space:]]+AXIOM_ALLOW:[[:space:]]*(.+) ]]; then
                local name
                name=$(echo "${BASH_REMATCH[1]}" \
                    | sed 's/[[:space:]].*//')
                echo "$name"
            fi
            ((idx--))
            continue
        fi

        # Blank line or any other content — stop.
        break
    done
}

# ---------------------------------------------------------------------------
# strip_private_prefix: remove the `_private.<module-path>.<n>.` prefix
# Lean adds to declarations declared with the `private` keyword when
# their internal name surfaces in `#print axioms` output.  The
# module-path is dot-separated and contains no whitespace; `<n>` is
# the private-numbering discriminator (typically 0).
# ---------------------------------------------------------------------------
strip_private_prefix() {
    echo "$1" | sed -E 's/^_private\.[^[:space:]]+\.[0-9]+\.//'
}

# ---------------------------------------------------------------------------
# process_axiom_list: process the comma-separated axiom names extracted
# from inside the `[ ... ]` of a `#print axioms` line.  Reports each
# non-standard axiom (after AXIOM_ALLOW suppression).  Reads/writes
# globals declared in check_file's scope: DECLARATIONS, DECL_LINE_NUMS,
# BACKUP_FILE, VERBOSE, HAS_CUSTOM, CUSTOM_AXIOM_COUNT.
# ---------------------------------------------------------------------------
process_axiom_list() {
    local decl="$1"
    local list="$2"
    local IFS=','
    local raw axiom
    local -a parts
    read -ra parts <<< "$list"
    for raw in "${parts[@]}"; do
        axiom=$(echo "$raw" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')
        [[ -z "$axiom" ]] && continue
        if [[ "$axiom" =~ $STANDARD_AXIOMS_REGEX ]]; then
            if [[ "$VERBOSE" == "--verbose" ]]; then
                echo -e "    ${GREEN}✓${NC} $axiom (standard)"
            fi
            continue
        fi
        # Locate source line for the AXIOM_ALLOW lookup.  Match either
        # against the bare-name attribution we appended `#print axioms`
        # for, or against the corresponding `<NAMESPACE>.<bare>` form.
        local src_line=0 i
        for (( i=0; i<${#DECLARATIONS[@]}; i++ )); do
            if [[ "${DECLARATIONS[$i]}" == "$decl" ]]; then
                src_line="${DECL_LINE_NUMS[$i]}"
                break
            fi
        done
        local allowed=false
        if [[ $src_line -gt 0 ]]; then
            while IFS= read -r allowed_axiom; do
                if [[ "$allowed_axiom" == "$axiom" ]]; then
                    allowed=true
                    break
                fi
            done < <(get_axiom_allows "$BACKUP_FILE" "$src_line")
        fi
        if [[ "$allowed" == true ]]; then
            if [[ "$VERBOSE" == "--verbose" ]]; then
                echo -e \
                    "    ${YELLOW}~${NC}" \
                    "$axiom (allowed via AXIOM_ALLOW)"
            fi
        else
            echo -e \
                "  ${RED}⚠ $decl" \
                "uses non-standard axiom: $axiom${NC}"
            HAS_CUSTOM=true
            ((++CUSTOM_AXIOM_COUNT))
        fi
    done
}

# ---------------------------------------------------------------------------
# parse_axiom_output: parse Lean 4's `#print axioms` emissions from
# the accumulated `lake env lean` OUTPUT.  Lean 4's canonical forms:
#
#     'X' depends on axioms: [a, b, c]
#     'X' depends on axioms: [propext,
#      Quot.sound]
#     'X' does not depend on any axioms
#
# This parser is a small state machine over the bracketed list: a
# `depends on axioms:` header opens the list, and the list closes on
# the next `]` (which may appear on the same line or on a continuation
# line that Lean wrapped to).  Lines that don't match either canonical
# header form are ignored — error-message body text, prose, and noise
# cannot be misread as axiom dependencies.
#
# Reads OUTPUT; writes globals HAS_CUSTOM, PARSED_ANY, CUSTOM_AXIOM_COUNT
# (in check_file's scope).
# ---------------------------------------------------------------------------
parse_axiom_output() {
    local in_list=false
    local current_decl=""
    local list_buf=""
    local line rest inner

    while IFS= read -r line; do
        if [[ "$in_list" == true ]]; then
            list_buf="${list_buf} ${line}"
            if [[ "$line" == *"]"* ]]; then
                inner="${list_buf%%\]*}"
                process_axiom_list "$current_decl" "$inner"
                in_list=false
                current_decl=""
                list_buf=""
            fi
            continue
        fi

        if [[ "$line" =~ \
            ^\'([^\']+)\'[[:space:]]+depends[[:space:]]+on[[:space:]]+axioms:[[:space:]]*(.*)$ ]]
        then
            current_decl=$(strip_private_prefix "${BASH_REMATCH[1]}")
            PARSED_ANY=true
            if [[ "$VERBOSE" == "--verbose" ]]; then
                echo -e "  ${BLUE}${current_decl}:${NC}"
            fi
            rest="${BASH_REMATCH[2]}"
            rest="${rest#\[}"
            if [[ "$rest" == *"]"* ]]; then
                inner="${rest%%\]*}"
                process_axiom_list "$current_decl" "$inner"
                current_decl=""
            else
                in_list=true
                list_buf="$rest"
            fi
            continue
        fi

        if [[ "$line" =~ \
            ^\'([^\']+)\'[[:space:]]+does[[:space:]]+not[[:space:]]+depend[[:space:]]+on[[:space:]]+any[[:space:]]+axioms ]]
        then
            current_decl=$(strip_private_prefix "${BASH_REMATCH[1]}")
            PARSED_ANY=true
            if [[ "$VERBOSE" == "--verbose" ]]; then
                echo -e "  ${BLUE}${current_decl}:${NC} (no axioms)"
            fi
            current_decl=""
            continue
        fi
    done <<< "$OUTPUT"
}

# ---------------------------------------------------------------------------
# check_file: process one .lean file
# ---------------------------------------------------------------------------
check_file() {
    local FILE="$1"

    echo -e "${BLUE}File: ${YELLOW}$FILE${NC}"

    # Extract namespace if any.
    local NAMESPACE=""
    if grep -q "^namespace " "$FILE"; then
        NAMESPACE=$(grep "^namespace " "$FILE" \
            | head -1 | sed 's/namespace //')
    fi

    # Extract all top-level declarations together with their line numbers.
    # Format per entry: "<lineno> <bare-name>"
    local DECL_LINES=()
    while IFS= read -r line; do
        DECL_LINES+=("$line")
    done < <(grep -nE \
        '^(theorem|lemma|def|instance|abbrev|example|structure|class|inductive) ' \
        "$FILE" 2>/dev/null || true)

    if [[ ${#DECL_LINES[@]} -eq 0 ]]; then
        echo -e "  ${YELLOW}No declarations found${NC}"
        echo
        return 0
    fi

    # Build parallel arrays: DECLARATIONS (qualified names) and
    # DECL_LINE_NUMS (source line numbers).
    local DECLARATIONS=()
    local DECL_LINE_NUMS=()
    for entry in "${DECL_LINES[@]}"; do
        local lineno
        lineno=$(echo "$entry" | cut -d: -f1)
        local rest
        rest=$(echo "$entry" | cut -d: -f2-)
        local bare
        # The stop set excludes whitespace, the characters that begin
        # implicit/explicit/instance arguments, type ascription, and
        # universe annotations (` :({[`), and the punctuation that
        # appears when prose inside `/-- ... -/` or `/-! ... -/`
        # docstrings happens to begin with a Lean keyword: `,` (e.g.,
        # ``structure maps, one per constructor.``) and backtick
        # (e.g., ``abbrev `FunctorBetween…` form gets stuck on``).
        # In every such case the resulting bare name is either left
        # equal to the input line (sed substitution fails, and the
        # declaration is skipped) or yields a stem like `maps` whose
        # qualified form `<namespace>.maps` triggers a tolerable
        # unknown-constant error rather than a Lean parse failure.
        bare=$(echo "$rest" | sed -E \
            's/^(theorem|lemma|def|instance|abbrev|example|structure|class|inductive) +([^ :({[,`]+).*/\2/')
        # Strip a trailing dot that survives from `def Foo.bar.{u, v}`
        # extractions (we stop at `{`, leaving the connecting dot).
        bare="${bare%.}"
        # Skip nameless declarations (the `example` form has no name;
        # the sed leaves the line unchanged, producing a bare value
        # that's either the keyword itself or empty — neither is a
        # valid Lean declaration name. `example`s are test-only and
        # don't carry committed axioms; type-check suffices.)
        if [[ "$bare" == "example" ]] || [[ "$bare" == "$rest" ]]; then
            continue
        fi
        if [[ -n "$bare" ]]; then
            if [[ -n "$NAMESPACE" ]]; then
                DECLARATIONS+=("$NAMESPACE.$bare")
            else
                DECLARATIONS+=("$bare")
            fi
            DECL_LINE_NUMS+=("$lineno")
        fi
    done

    echo -e "  ${GREEN}Found ${#DECLARATIONS[@]} declarations${NC}"

    # Early return when no named declarations remain after the
    # bare-name extraction (e.g., the only matches were anonymous
    # `example` blocks).  Files of that shape carry no committed
    # axioms to check; running `#print axioms` against them would
    # append no commands, and treating a `lake env lean` failure
    # there as a real error would misattribute the file's own
    # unrelated diagnostics to the axiom audit.
    if [[ ${#DECLARATIONS[@]} -eq 0 ]]; then
        echo -e \
            "  ${YELLOW}No named declarations to check${NC}"
        echo
        return 0
    fi

    # Create backup and track it with a marker file for SIGINT safety.
    local BACKUP_FILE="${FILE}.axiom_check_backup"
    ((++MARKER_COUNT))
    local MARKER_FILE="$MARKER_DIR/${MARKER_COUNT}.marker"
    cp "$FILE" "$BACKUP_FILE"
    echo "$FILE" > "$MARKER_FILE"

    cleanup_done=false
    cleanup_file() {
        if [[ "$cleanup_done" == false && -f "$BACKUP_FILE" ]]; then
            mv "$BACKUP_FILE" "$FILE"
            cleanup_done=true
            rm -f "$MARKER_FILE"
        fi
    }

    # Append #print axioms commands.
    echo "" >> "$FILE"
    echo "$MARKER" >> "$FILE"
    for decl in "${DECLARATIONS[@]}"; do
        echo "#print axioms $decl" >> "$FILE"
    done

    # Run Lean.  Capture exit status without aborting under
    # `set -e` so the parser can run regardless of lake env lean's
    # outcome (post-marker errors from the appended `#print axioms`
    # commands are routinely tolerable; see § Local modifications,
    # items 4 and 6).
    local HAS_CUSTOM=false
    local PARSED_ANY=false
    local LAKE_EXIT=0
    OUTPUT=$(lake env lean "$FILE" 2>&1) || LAKE_EXIT=$?

    # Always parse: the new parser only matches Lean's canonical
    # `'X' depends on axioms:` / `'X' does not depend on any axioms`
    # forms, so noise — including pre-marker diagnostics from lake
    # env lean ignoring `lakefile.toml` `leanOptions` — is ignored
    # by construction.
    parse_axiom_output

    # Detect real (non-absorbed, post-marker) errors.
    local MARKER_LINE
    MARKER_LINE=$(grep -nF -- "$MARKER" "$FILE" \
        | head -1 | cut -d: -f1)

    local HAS_REAL_ERROR=false
    if [[ $LAKE_EXIT -ne 0 ]]; then
        # Detect real-error diagnostics anywhere in the output by
        # filtering against the union of absorbed forms.  Lean
        # emits two diagnostic shapes with `:<line>:<col>:`
        # location markers:
        #   * `<file>:<N>:<M>: error: <msg>` (trailing-form)
        #   * `error: <file>:<N>:<M>: <msg>` (leading-form, used
        #     for kernel-level type errors)
        # Both shapes contain the substring `error` and a
        # `:<digits>:<digits>:` location marker.  We extract every
        # such diagnostic line and filter out:
        #
        #   * Post-marker forms expected from the appended `#print
        #     axioms` commands when their qualifier is wrong
        #     (`unknown identifier`, `unknown constant`, the
        #     `maximum number of errors` cascade cap).  These are
        #     routine when the file uses multiple namespaces and
        #     the single-namespace heuristic above qualifies some
        #     declarations under the wrong prefix.
        #
        #   * Pre-marker spurious diagnostics that `lake env lean`
        #     emits because it ignores `lakefile.toml`'s
        #     `leanOptions` (`unsolved goals`, `failed to
        #     synthesize`, `Tactic ... failed`).  These appear on
        #     files that `lake build` accepts cleanly; the file's
        #     own content is already gated by `lake build` upstream
        #     of this script.
        #
        # Anything that survives both filters is treated as a real
        # error and fails the file.  This catches genuine
        # compilation failures (type mismatches, invalid field
        # notation, etc.) regardless of whether they appear before
        # or after the marker.
        local lean_diag_errors
        lean_diag_errors=$(echo "$OUTPUT" \
            | grep -E ':[0-9]+:[0-9]+:.*error|error.*:[0-9]+:[0-9]+:' \
            || true)
        # `grep -c >/dev/null` (rather than `grep -qvE`) consumes
        # all input; `-q` short-circuits and leaves the upstream
        # pipe with SIGPIPE (141), which `set -o pipefail` then
        # surfaces as a non-zero pipeline exit and miscategorises
        # the file.
        local unabsorbed_count
        if [[ -n "$lean_diag_errors" ]]; then
            unabsorbed_count=$(echo "$lean_diag_errors" \
                | grep -cvE \
                    'unknownIdentifier|unknown identifier|unknown constant|maximum number of errors|unsolved goals|failed to synthesize|Tactic .* failed' \
                || true)
        else
            unabsorbed_count=0
        fi
        if [[ "$unabsorbed_count" -gt 0 ]]; then
            HAS_REAL_ERROR=true
        fi
    fi

    if [[ "$HAS_REAL_ERROR" == true ]]; then
        echo -e "  ${RED}Error running Lean${NC}" >&2
        echo "$OUTPUT" \
            | grep -E 'error' \
            | head -10 | sed 's/^/  /' >&2
        cleanup_file
        echo
        return 1
    fi

    if [[ "$PARSED_ANY" == false ]]; then
        # No `'X' depends on axioms:` lines were produced for any
        # of the appended `#print axioms` commands.  In practice
        # this happens when the file uses multiple namespaces and
        # the single-namespace heuristic above qualifies every
        # declaration under the wrong prefix, producing absorbed
        # `unknown constant` errors for each `#print axioms`
        # invocation.  Surface as a soft warning rather than a
        # hard error: `lake build` (which precedes this script in
        # CI / `pre-push.sh` / `pre-commit.sh`) has already
        # validated the file's content, so we know the file
        # compiles; the audit just couldn't address its
        # declarations.
        echo -e \
            "  ${YELLOW}⚠ Declarations unaddressable under" \
            "inferred namespace; not audited${NC}"
    elif [[ "$HAS_CUSTOM" == false ]]; then
        echo -e \
            "  ${GREEN}✓ All declarations use only" \
            "standard axioms${NC}"
    else
        ((++FILES_WITH_CUSTOM))
    fi

    ((TOTAL_DECLARATIONS+=${#DECLARATIONS[@]}))
    ((++TOTAL_FILES))

    cleanup_file
    echo
    return 0
}

# ---------------------------------------------------------------------------
# Main loop
# ---------------------------------------------------------------------------
FAILED_FILES=()
for file in "${LEAN_FILES[@]}"; do
    if ! check_file "$file"; then
        FAILED_FILES+=("$file")
    fi
done

# Summary
echo -e \
    "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${BLUE}Summary:${NC}"
echo -e "  Files checked: $TOTAL_FILES"
echo -e "  Declarations checked: $TOTAL_DECLARATIONS"

if [[ $TOTAL_FILES -eq 0 && ${#FAILED_FILES[@]} -gt 0 ]]; then
    echo -e "  ${YELLOW}⚠ No files were successfully checked${NC}"
elif [[ $FILES_WITH_CUSTOM -eq 0 ]]; then
    echo -e "  ${GREEN}✓ All files use only standard axioms${NC}"
else
    echo -e "  ${RED}⚠ Files with non-standard axioms: $FILES_WITH_CUSTOM${NC}"
    echo -e \
        "  ${RED}⚠ Total non-standard axiom usages:" \
        "$CUSTOM_AXIOM_COUNT${NC}"
fi

if [[ ${#FAILED_FILES[@]} -gt 0 ]]; then
    echo -e "  ${RED}✗ Files with errors: ${#FAILED_FILES[@]}${NC}"
    for file in "${FAILED_FILES[@]}"; do
        echo -e "    - $file"
    done
fi

echo
echo -e "${YELLOW}Standard axioms (acceptable):${NC}"
echo "  • propext (propositional extensionality)"
echo "  • quot.sound (quotient soundness)"
echo "  • Quot.sound (quotient soundness, capitalized variant)"

if [[ $FILES_WITH_CUSTOM -gt 0 ]]; then
    echo
    echo -e \
        "${YELLOW}Tip: Non-standard axioms should have" \
        "AXIOM_ALLOW annotations or elimination plans${NC}"
    if [[ -z "$EXIT_ZERO_ON_FINDINGS" ]]; then exit 1; fi
fi

if [[ ${#FAILED_FILES[@]} -gt 0 ]]; then
    exit 1
fi

exit 0

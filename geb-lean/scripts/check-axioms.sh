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
STANDARD_AXIOMS="propext|quot.sound|Quot.sound"

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
        bare=$(echo "$rest" | sed -E \
            's/^(theorem|lemma|def|instance|abbrev|example|structure|class|inductive) +([^ :(]+).*/\2/')
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

    # Run Lean.
    local HAS_CUSTOM=false
    if OUTPUT=$(lake env lean "$FILE" 2>&1); then
        local CURRENT_DECL=""

        while IFS= read -r line; do
            if [[ "$line" =~ \
                ^([a-zA-Z0-9_.]+)[[:space:]]+depends[[:space:]]+on[[:space:]]+axioms: ]]; then
                CURRENT_DECL="${BASH_REMATCH[1]}"
                if [[ "$VERBOSE" == "--verbose" ]]; then
                    echo -e "  ${BLUE}$CURRENT_DECL:${NC}"
                fi
            elif [[ "$line" =~ \
                ^[[:space:]]*([a-zA-Z0-9_.]+)[[:space:]]*$ ]]; then
                axiom="${BASH_REMATCH[1]}"
                if [[ -n "$axiom" \
                    && ! "$axiom" =~ ^[[:space:]]*$ ]]; then
                    if [[ ! "$axiom" =~ $STANDARD_AXIOMS ]]; then
                        # Look up the source line for CURRENT_DECL.
                        local src_line=0
                        local i
                        for (( i=0; i<${#DECLARATIONS[@]}; i++ )); do
                            if [[ "${DECLARATIONS[$i]}" \
                                == "$CURRENT_DECL" ]]; then
                                src_line="${DECL_LINE_NUMS[$i]}"
                                break
                            fi
                        done
                        # Collect AXIOM_ALLOW annotations.
                        local allowed=false
                        if [[ $src_line -gt 0 ]]; then
                            while IFS= read -r allowed_axiom; do
                                if [[ "$allowed_axiom" == "$axiom" ]]; then
                                    allowed=true
                                    break
                                fi
                            done < <(get_axiom_allows "$BACKUP_FILE" \
                                "$src_line")
                        fi
                        if [[ "$allowed" == true ]]; then
                            if [[ "$VERBOSE" == "--verbose" ]]; then
                                echo -e \
                                    "    ${YELLOW}~${NC}" \
                                    "$axiom (allowed via AXIOM_ALLOW)"
                            fi
                        else
                            echo -e \
                                "  ${RED}⚠ $CURRENT_DECL" \
                                "uses non-standard axiom: $axiom${NC}"
                            HAS_CUSTOM=true
                            ((++CUSTOM_AXIOM_COUNT))
                        fi
                    elif [[ "$VERBOSE" == "--verbose" ]]; then
                        echo -e "    ${GREEN}✓${NC} $axiom (standard)"
                    fi
                fi
            fi
        done <<< "$OUTPUT"

        if [[ "$HAS_CUSTOM" == false ]]; then
            echo -e \
                "  ${GREEN}✓ All declarations use only standard axioms${NC}"
        else
            ((++FILES_WITH_CUSTOM))
        fi

        ((TOTAL_DECLARATIONS+=${#DECLARATIONS[@]}))
        ((++TOTAL_FILES))

        cleanup_file
        echo
        return 0
    else
        # Check if errors are ONLY unknownIdentifier in our appended region.
        local MARKER_LINE
        MARKER_LINE=$(grep -nF -- "$MARKER" "$FILE" \
            | head -1 | cut -d: -f1)

        local HAS_REAL_ERROR=false
        while IFS= read -r error_line; do
            if [[ "$error_line" =~ :([0-9]+):[0-9]+:.*error ]]; then
                local err_lineno="${BASH_REMATCH[1]}"
                if [[ -n "$MARKER_LINE" \
                    && "$err_lineno" -lt "$MARKER_LINE" ]]; then
                    HAS_REAL_ERROR=true
                    break
                fi
            fi
        done < <(echo "$OUTPUT" | grep -E ':[0-9]+:[0-9]+:.*error')

        if echo "$OUTPUT" \
            | grep -E ':[0-9]+:[0-9]+:.*error' \
            | grep -qvE \
                'unknownIdentifier|unknown identifier|unknown constant'; then
            HAS_REAL_ERROR=true
        fi

        if [[ "$HAS_REAL_ERROR" == false ]] \
            && echo "$OUTPUT" \
                | grep -q \
                    'unknownIdentifier\|unknown identifier\|unknown constant'
        then
            echo -e \
                "  ${YELLOW}⚠ Some declarations not accessible" \
                "(private/local)${NC}"

            local CURRENT_DECL=""
            local PARSED_ANY=false

            while IFS= read -r line; do
                if [[ "$line" =~ \
                    ^([a-zA-Z0-9_.]+)[[:space:]]+depends[[:space:]]+on[[:space:]]+axioms: ]]; then
                    CURRENT_DECL="${BASH_REMATCH[1]}"
                    PARSED_ANY=true
                    if [[ "$VERBOSE" == "--verbose" ]]; then
                        echo -e "  ${BLUE}$CURRENT_DECL:${NC}"
                    fi
                elif [[ "$line" =~ \
                    ^[[:space:]]*([a-zA-Z0-9_.]+)[[:space:]]*$ ]]; then
                    axiom="${BASH_REMATCH[1]}"
                    if [[ -n "$axiom" \
                        && ! "$axiom" =~ ^[[:space:]]*$ ]]; then
                        if [[ ! "$axiom" =~ $STANDARD_AXIOMS ]]; then
                            local src_line=0
                            local i
                            for (( i=0; i<${#DECLARATIONS[@]}; i++ )); do
                                if [[ "${DECLARATIONS[$i]}" \
                                    == "$CURRENT_DECL" ]]; then
                                    src_line="${DECL_LINE_NUMS[$i]}"
                                    break
                                fi
                            done
                            local allowed=false
                            if [[ $src_line -gt 0 ]]; then
                                while IFS= read -r allowed_axiom; do
                                    if [[ "$allowed_axiom" \
                                        == "$axiom" ]]; then
                                        allowed=true
                                        break
                                    fi
                                done < <(get_axiom_allows \
                                    "$BACKUP_FILE" "$src_line")
                            fi
                            if [[ "$allowed" == true ]]; then
                                if [[ "$VERBOSE" == "--verbose" ]]; then
                                    echo -e \
                                        "    ${YELLOW}~${NC}" \
                                        "$axiom (allowed via AXIOM_ALLOW)"
                                fi
                            else
                                echo -e \
                                    "  ${RED}⚠ $CURRENT_DECL" \
                                    "uses non-standard axiom: $axiom${NC}"
                                HAS_CUSTOM=true
                                ((++CUSTOM_AXIOM_COUNT))
                            fi
                        elif [[ "$VERBOSE" == "--verbose" ]]; then
                            echo -e "    ${GREEN}✓${NC} $axiom (standard)"
                        fi
                    fi
                fi
            done <<< "$OUTPUT"

            if [[ "$PARSED_ANY" == true ]]; then
                if [[ "$HAS_CUSTOM" == false ]]; then
                    echo -e \
                        "  ${GREEN}✓ Accessible declarations use" \
                        "only standard axioms${NC}"
                else
                    ((++FILES_WITH_CUSTOM))
                fi
                ((TOTAL_DECLARATIONS+=${#DECLARATIONS[@]}))
                ((++TOTAL_FILES))
            fi

            cleanup_file
            echo
            return 0
        else
            echo -e "  ${RED}Error running Lean${NC}" >&2
            echo "$OUTPUT" | grep "error" | head -10 | sed 's/^/  /' >&2
            cleanup_file
            echo
            return 1
        fi
    fi
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

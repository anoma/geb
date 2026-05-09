#!/usr/bin/env bash
# block-mutating-git.sh — PreToolUse hook for Claude Code.
# Default-deny gate on raw `git` invocations.  Read-only subcommands and
# a small set of closed allowlists are permitted; everything else is
# blocked with exit 2 and a translation message to stderr.

set -u

# ---------------------------------------------------------------------------
# Read the PreToolUse JSON payload from stdin.
# ---------------------------------------------------------------------------

payload=$(cat)

tool_name=$(printf '%s' "$payload" | jq -r '.tool_name // empty')
command=$(printf '%s' "$payload" | jq -r '.tool_input.command // empty')

# Only inspect Bash tool calls.
if [[ "$tool_name" != "Bash" ]]; then
  exit 0
fi

# If the command is empty there is nothing to inspect.
if [[ -z "$command" ]]; then
  exit 0
fi

# ---------------------------------------------------------------------------
# Tokenise the command string with whitespace splitting.
# ---------------------------------------------------------------------------

read -ra tokens <<< "$command"

# ---------------------------------------------------------------------------
# jj git stripping: if .jj/ exists, allow jj-mediated git interop outright.
# ---------------------------------------------------------------------------

project_dir="${CLAUDE_PROJECT_DIR:-$PWD}"
if [[ -d "$project_dir/.jj" ]]; then
  # If the first token is "jj" and the second is "git", pass through.
  if [[ "${tokens[0]:-}" == "jj" && "${tokens[1]:-}" == "git" ]]; then
    exit 0
  fi
fi

# ---------------------------------------------------------------------------
# Find the position of "git" in the token array, and build the argv that
# git itself sees (everything after "git", option flags included, but
# excluding any shell-level env-var assignments that precede the command).
# For example:
#   GIT_DIR=/tmp git status  →  argv = (status)
#   git -C /some/path log    →  argv = (-C /some/path log)
# We locate the first token that equals "git" and use the rest.
# ---------------------------------------------------------------------------

git_pos=-1
for i in "${!tokens[@]}"; do
  if [[ "${tokens[$i]}" == "git" ]]; then
    git_pos=$i
    break
  fi
done

# If there is no "git" token this hook has nothing to check.
if [[ $git_pos -lt 0 ]]; then
  exit 0
fi

# git_argv: everything after "git".
git_argv=("${tokens[@]:$((git_pos + 1))}")

# ---------------------------------------------------------------------------
# Strip leading git global options (-C <path>, --git-dir=, --work-tree=,
# --no-pager, -c key=val, etc.) to reach the subcommand.
# We only strip option clusters that appear before the subcommand word.
# ---------------------------------------------------------------------------

sub_pos=0   # index within git_argv of the subcommand
while [[ $sub_pos -lt ${#git_argv[@]} ]]; do
  tok="${git_argv[$sub_pos]}"
  case "$tok" in
    -C | --git-dir | --work-tree | -c | --namespace | --super-prefix)
      # These take a following argument; skip two tokens.
      sub_pos=$((sub_pos + 2))
      ;;
    --git-dir=* | --work-tree=* | -c=* | --namespace=* | --super-prefix=*)
      # Inline value; skip one token.
      sub_pos=$((sub_pos + 1))
      ;;
    --no-pager | --no-replace-objects | --bare | --literal-pathspecs \
    | --glob-pathspecs | --noglob-pathspecs | --icase-pathspecs \
    | --no-optional-locks | --no-advice | -p | --paginate)
      # Boolean flags; skip one token.
      sub_pos=$((sub_pos + 1))
      ;;
    -*)
      # Unknown leading flag — skip it conservatively.
      sub_pos=$((sub_pos + 1))
      ;;
    *)
      # First non-option token is the subcommand.
      break
      ;;
  esac
done

subcommand="${git_argv[$sub_pos]:-}"
# Arguments to the subcommand (everything after the subcommand word).
sub_args=("${git_argv[@]:$((sub_pos + 1))}")

# ---------------------------------------------------------------------------
# Deny helper: writes a message to stderr and exits 2.
# Parameters: $1 = reason text, $2 (optional) = jj equivalent line.
# ---------------------------------------------------------------------------

deny() {
  local reason="$1"
  local jj_equiv="${2:-}"
  {
    printf 'block-mutating-git: blocked `git %s`\n' \
           "$subcommand${sub_args[*]:+ ${sub_args[*]}}"
    printf '  reason: %s\n' "$reason"
    if [[ -n "$jj_equiv" ]]; then
      printf '  jj equivalent: %s\n' "$jj_equiv"
    fi
    printf '  if this should be allowed, propose the addition in a refactor plan.\n'
  } >&2
  exit 2
}

# ---------------------------------------------------------------------------
# Short-form → long-form flag canonicalisation.
# Applied per-subcommand for only the flags that participate in allowlist
# matching.
# ---------------------------------------------------------------------------

# Canonicalise the sub_args array in-place for a given pair.
# Usage: canonicalise_flag <short> <long>
canonicalise_flag() {
  local short="$1" long="$2"
  local i
  for i in "${!sub_args[@]}"; do
    if [[ "${sub_args[$i]}" == "$short" ]]; then
      sub_args[$i]="$long"
    fi
  done
}

# ---------------------------------------------------------------------------
# Dispatch on subcommand.
# ---------------------------------------------------------------------------

case "$subcommand" in

  # -------------------------------------------------------------------------
  # Read-only subcommands — allow unconditionally.
  # -------------------------------------------------------------------------
  status | log | diff | show | blame | rev-parse | ls-files | ls-tree \
  | describe | cat-file | name-rev | reflog | grep | shortlog \
  | whatchanged | count-objects | verify-pack | verify-tag | version | help)
    exit 0
    ;;

  # -------------------------------------------------------------------------
  # remote — allow only `remote -v` / `remote --verbose`.
  # -------------------------------------------------------------------------
  remote)
    canonicalise_flag -v --verbose
    first_arg="${sub_args[0]:-}"
    if [[ "$first_arg" == "--verbose" ]]; then
      exit 0
    fi
    deny "only 'git remote --verbose (-v)' is on the allowlist" \
         "jj git remote list"
    ;;

  # -------------------------------------------------------------------------
  # branch — allow only `branch --list`.
  # -------------------------------------------------------------------------
  branch)
    canonicalise_flag -l --list
    # Remove any other flags that are not --list to check what remains.
    has_list=false
    has_mutating=false
    for arg in "${sub_args[@]}"; do
      case "$arg" in
        --list)
          has_list=true
          ;;
        --delete | -d | -D | --move | -m | -M | --copy | -c | -C \
        | --set-upstream-to | -u | --unset-upstream \
        | --edit-description)
          has_mutating=true
          ;;
      esac
    done
    if [[ "$has_list" == "true" && "$has_mutating" == "false" ]]; then
      exit 0
    fi
    deny "only 'git branch --list' is on the allowlist" \
         "jj branch list"
    ;;

  # -------------------------------------------------------------------------
  # tag — allow only `tag --list`.
  # -------------------------------------------------------------------------
  tag)
    canonicalise_flag -l --list
    has_list=false
    for arg in "${sub_args[@]}"; do
      if [[ "$arg" == "--list" ]]; then
        has_list=true
      fi
    done
    # Any other flag that might be mutating → deny.
    has_mutating=false
    for arg in "${sub_args[@]}"; do
      case "$arg" in
        --delete | -d | --sign | -s | --annotate | -a | -f | --force \
        | --create-reflog | --verify | --no-sign)
          has_mutating=true
          ;;
      esac
    done
    if [[ "$has_list" == "true" && "$has_mutating" == "false" ]]; then
      exit 0
    fi
    deny "tag operations (create, delete, push) are not on the allowlist; only 'git tag --list' is permitted" \
         "jj tag list"
    ;;

  # -------------------------------------------------------------------------
  # config — allow only --get, --list, --get-all.
  # -------------------------------------------------------------------------
  config)
    # Determine the first substantive flag (skip global-scope flags).
    first_flag=""
    for arg in "${sub_args[@]}"; do
      case "$arg" in
        --system | --global | --local | --worktree | --file | -f \
        | --blob | --includes | --no-includes | -z | --null \
        | --name-only | --show-origin | --show-scope | --type \
        | --bool | --int | --bool-or-int | --path | --expiry-date)
          # Scope / format modifiers; skip.
          continue
          ;;
        -*)
          first_flag="$arg"
          break
          ;;
        *)
          # Positional — means a setter like `git config section.key value`.
          first_flag="__positional__"
          break
          ;;
      esac
    done
    case "$first_flag" in
      --get | --list | --get-all)
        exit 0
        ;;
      "")
        # No flag at all — could be `git config` with only scope flags;
        # treat as a query only if there is exactly one positional following
        # scope flags (a plain key read).  Safer: deny any ambiguous form.
        deny "ambiguous 'git config' invocation; use --get, --list, or --get-all"
        ;;
      *)
        deny "only 'git config --get', 'git config --list', and 'git config --get-all' are on the allowlist; setter forms are blocked"
        ;;
    esac
    ;;

  # -------------------------------------------------------------------------
  # fetch — closed allowlist of three exact forms (after flag canonicalisation).
  # -------------------------------------------------------------------------
  fetch)
    # Canonicalise flags that appear in allowlist-adjacent positions.
    # (None of the three allowed forms use short flags, so no short→long mapping
    # is needed here; we simply reject any flag token outright.)

    # Collect positional (non-flag) arguments and flag arguments separately.
    positionals=()
    flags=()
    for arg in "${sub_args[@]}"; do
      if [[ "$arg" == -* ]]; then
        flags+=("$arg")
      else
        positionals+=("$arg")
      fi
    done

    n_pos=${#positionals[@]}
    n_flags=${#flags[@]}

    # Allowed forms have no flags at all.
    if [[ $n_flags -gt 0 ]]; then
      deny "git fetch with flags (--tags, --prune, --all, etc.) is not on the allowlist" \
           "jj git fetch"
    fi

    case $n_pos in
      0)
        # Bare `git fetch`
        exit 0
        ;;
      1)
        # `git fetch origin` — only the literal remote name "origin" is allowed.
        if [[ "${positionals[0]}" == "origin" ]]; then
          exit 0
        fi
        deny "only 'git fetch origin' is on the allowlist; other remotes are blocked" \
             "jj git fetch --remote origin"
        ;;
      2)
        # `git fetch origin refs/pull/*/head:*`
        if [[ "${positionals[0]}" == "origin" && \
              "${positionals[1]}" == "refs/pull/*/head:*" ]]; then
          exit 0
        fi
        deny "only 'git fetch origin refs/pull/*/head:*' is on the allowlist for two-argument fetch" \
             "jj git fetch --remote origin"
        ;;
      *)
        deny "git fetch with more than two positional arguments is not on the allowlist" \
             "jj git fetch"
        ;;
    esac
    ;;

  # -------------------------------------------------------------------------
  # clone — allowed only when target resolves outside $PWD tree.
  # -------------------------------------------------------------------------
  clone)
    # Collect positional (non-flag) arguments to locate URL and target.
    # We do minimal flag parsing: flags with a following value consume two
    # tokens; boolean flags consume one.
    positionals=()
    i=0
    while [[ $i -lt ${#sub_args[@]} ]]; do
      tok="${sub_args[$i]}"
      case "$tok" in
        # Flags that take a following value argument.
        --template | --reference | --reference-if-able | --origin | -o \
        | --branch | -b | --upload-pack | -u | --depth \
        | --shallow-since | --shallow-exclude | --recurse-submodules \
        | --separate-git-dir | -j | --jobs | --filter \
        | --bundle-uri)
          i=$((i + 2))
          ;;
        # Boolean flags.
        -l | --local | -s | --shared | -n | --no-checkout \
        | --bare | --mirror | --dissociate | -q | --quiet \
        | -v | --verbose | --progress | --no-single-branch \
        | --single-branch | --no-tags | --shallow-submodules \
        | --no-shallow-submodules | --remote-submodules \
        | --no-remote-submodules | --sparse)
          i=$((i + 1))
          ;;
        -*)
          # Unknown flag — skip conservatively.
          i=$((i + 1))
          ;;
        *)
          positionals+=("$tok")
          i=$((i + 1))
          ;;
      esac
    done

    # positionals[0] = URL, positionals[1] = target dir (optional).
    n_pos=${#positionals[@]}
    if [[ $n_pos -eq 0 ]]; then
      # No URL given — this will fail for git anyway; deny.
      deny "git clone requires at least a URL argument"
      exit 2
    fi

    url="${positionals[0]}"

    if [[ $n_pos -ge 2 ]]; then
      target_raw="${positionals[1]}"
    else
      # Default: git uses the last component of the URL, minus .git suffix.
      url_basename="${url##*/}"
      target_raw="${url_basename%.git}"
      # Resolve relative to PWD.
      target_raw="./$target_raw"
    fi

    # Resolve the target to an absolute path (using -m so non-existent is OK).
    target_abs=$(realpath -m "$target_raw")

    if [[ "$target_abs" == "$PWD" || "$target_abs" == "$PWD/"* ]]; then
      deny "git clone target '$target_raw' resolves to or inside \$PWD ($PWD); self-clobbering clones are not allowed" \
           "jj git clone <url> <dir-outside-project>"
    fi

    # Also block cloning FROM the current directory into another place if
    # the URL is the current directory, as that is unusual and likely a mistake.
    url_abs=$(realpath -m "$url" 2>/dev/null || printf '%s' "$url")
    if [[ "$url_abs" == "$PWD" ]]; then
      deny "git clone source is \$PWD itself; this form is not on the allowlist"
    fi

    exit 0
    ;;

  # -------------------------------------------------------------------------
  # Default: deny everything else.
  # -------------------------------------------------------------------------
  "")
    deny "bare 'git' invocation with no subcommand"
    ;;
  *)
    # Map common mutating subcommands to jj equivalents for the message.
    case "$subcommand" in
      add)
        jj_hint="jj file track <path>"
        ;;
      commit)
        jj_hint="jj commit  or  jj describe"
        ;;
      push)
        jj_hint="jj git push"
        ;;
      pull)
        jj_hint="jj git fetch  then  jj rebase"
        ;;
      merge)
        jj_hint="jj rebase -d <target>  then resolve conflicts"
        ;;
      rebase)
        jj_hint="jj rebase"
        ;;
      reset)
        jj_hint="jj restore  or  jj abandon"
        ;;
      checkout | switch)
        jj_hint="jj new <target>  or  jj edit <rev>"
        ;;
      restore)
        jj_hint="jj restore <path>"
        ;;
      cherry-pick)
        jj_hint="jj cherry-pick  (or duplicate + rebase)"
        ;;
      stash)
        jj_hint="jj new  (work in a new change instead)"
        ;;
      rm)
        jj_hint="jj file untrack <path>  or  remove the file directly"
        ;;
      mv)
        jj_hint="mv <src> <dst>  (jj tracks by content)"
        ;;
      *)
        jj_hint=""
        ;;
    esac
    deny "subcommand '$subcommand' is not on the read-only allowlist" "$jj_hint"
    ;;
esac

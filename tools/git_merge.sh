#!/usr/bin/env bash
# Merge an accepted pull request with git, when GitHub's merge API refuses this workflow's token ("Resource not
# accessible by integration": #7514, #7562, #7031, ... were accepted on 27 November and never merged).
# Called by tools/verdict_one.sh after every one of its checks passed (one-file rule from the merge ref, head pinned,
# trusted re-lint, shortest-proof rule); trusted: it never runs pull request code. Each merge is one commit on top of
# main whose tree is main's plus exactly the checked file (the blob at HEAD_SHA), with the pull request's head as second
# parent, so GitHub marks the pull request merged (its head becomes part of main); the commit is checked to change that
# one path and nothing else, and the duplicate and shortest-proof rules are applied again against main as it is at push
# time. Pushes never force (a moved main means start again).
# Group commit (v2): the merger's slots no longer push one by one. Each slot leaves its request in a spool and waits for
# the main lock; whoever takes the lock first fetches main once, builds one merge commit per waiting request on top of
# the previous one (same checks for each, against the tip of the chain), pushes the chain once and writes every slot its
# result. One push for many merges: the push is no longer the ceiling, and main gets far fewer pushes (each push also
# starts the workflows that run on pushes to main). A request whose objects cannot be fetched, or a chain that GitHub
# refuses for any reason other than a moved main, goes back to the slot, which merges alone as before.
# If GitHub refuses a two-parent push (a token that may not add the head's history), the same tree goes in as a
# single-parent commit and the pull request is closed with a pointer to it (one-by-one path only).
# Prints the new commit on success. Exit 2: not merged for a rule (already on main, not shorter), 1: failure.
# Needs: REPO PR HEAD_SHA FPATH MODE (new|replace) TITLE; base/ (a checkout of main whose credentials can push).
set -uo pipefail
G="git -C base"
fail() { echo "$1" >&2; exit "${2:-1}"; }
[[ "$PR" =~ ^[0-9]+$ && "$HEAD_SHA" =~ ^[0-9a-f]{40}$ ]] || fail "bad arguments"
[[ "$MODE" = new || "$MODE" = replace ]] || fail "bad mode"
printf '%s' "$FPATH" | grep -Eq "^(proofs|reductions|statements)/[A-Za-z0-9_.'-]+\.lean$" || fail "bad path"
# the head may not have moved since the check
[ "$($G ls-remote origin "refs/pull/$PR/head" 2>/dev/null | cut -f1)" = "$HEAD_SHA" ] || fail "the pull request's head moved"
$G cat-file -e "$HEAD_SHA^{commit}" 2>/dev/null || $G fetch -q --no-tags --depth 1 origin "refs/pull/$PR/head" || fail "cannot fetch the head"
BLOB=$($G rev-parse "$HEAD_SHA:$FPATH" 2>/dev/null) || fail "the file is not in the head"
MSG="${TITLE:-$FPATH} (#$PR)"
ID=(-c user.name="github-actions[bot]" -c user.email="41898282+github-actions[bot]@users.noreply.github.com")
# one merge of a given file at a time on this runner (the merger works several pull requests at once, oldest first):
# two copies of the same proof never race (nor sit in the same chain), and the one taken first (the older) goes first
exec 9> "/tmp/oma-git-merge-$(printf '%s' "$FPATH" | sha1sum | cut -c1-16).lock"; flock -w 600 9 || fail "file locked"
# One push to main at a time on this runner (global lock, taken after the file lock, always in that order: no deadlock).
exec 8> /tmp/oma-git-merge-main.lock
# What GitHub answers when main moved under a push (start again on the new main). Not "rejected" alone: a refusal such
# as a missing permission also says "[remote rejected] ... main" and retrying it ten times changes nothing.
RACE="fetch first|non-fast-forward|failed to update ref|cannot lock|incorrect old value"

# The one-by-one merge (v1), used when the group commit hands a request back.
merge_alone() {
  local TRY C OUT MAIN CHANGES TREE RES
  for TRY in 1 2 3 4 5 6 7 8 9 10; do
    flock -w 900 8 || fail "main locked"
    $G fetch -q --no-tags --depth 1 origin main || { flock -u 8; sleep 5; continue; }
    MAIN=$($G rev-parse FETCH_HEAD)
    if $G cat-file -e "$MAIN:$FPATH" 2>/dev/null; then
      [ "$MODE" = replace ] || fail "already on main" 2
      $G show "$MAIN:$FPATH" > gm_old.lean; $G show "$BLOB" > gm_new.lean
      read -r RES _ _ < <(python3 -I base/tools/prooflen.py gm_old.lean gm_new.lean)
      [ "$RES" = shorter ] || fail "not shorter than the proof on main" 2
    fi
    export GIT_INDEX_FILE="$PWD/gm_index"; rm -f "$GIT_INDEX_FILE"
    $G read-tree "$MAIN" && $G update-index --add --cacheinfo "100644,$BLOB,$FPATH" && TREE=$($G write-tree) || fail "cannot build the tree"
    unset GIT_INDEX_FILE
    CHANGES=$($G diff-tree -r --name-status "$MAIN" "$TREE")
    [ "$CHANGES" = "$(printf 'A\t%s' "$FPATH")" ] || [ "$CHANGES" = "$(printf 'M\t%s' "$FPATH")" ] || fail "unexpected change: $CHANGES"
    C=$($G "${ID[@]}" commit-tree "$TREE" -p "$MAIN" -p "$HEAD_SHA" -m "$MSG") || fail "cannot commit"
    if OUT=$($G -c push.negotiate=true push -q origin "$C:refs/heads/main" 2>&1); then echo "$C"; exit 0; fi
    if printf '%s' "$OUT" | grep -qiE "$RACE"; then
      flock -u 8; sleep 1; continue
    fi
    echo "two-parent push refused: ${OUT:0:200}" >&2
    C=$($G "${ID[@]}" commit-tree "$TREE" -p "$MAIN" -m "$MSG") || fail "cannot commit"
    if OUT=$($G push -q origin "$C:refs/heads/main" 2>&1); then
      gh api -X PATCH "repos/$REPO/pulls/$PR" -f state=closed >/dev/null 2>&1 || true
      echo "$C"; exit 0
    fi
    printf '%s' "$OUT" | grep -qiE "fetch first|non-fast-forward" && { flock -u 8; sleep 1; continue; }
    fail "push refused: ${OUT:0:200}"
  done
  fail "main kept moving"
}
[ -n "${OMA_MERGE_ALONE:-}" ] && merge_alone

# --- group commit ---
Q=/tmp/oma-merge-spool; mkdir -p "$Q/req" "$Q/res"
RID="$(date +%s%N).$PR.$$"
# The leader takes this head from this slot's own repository (a local fetch, a fraction of a second) instead of
# fetching it from GitHub again: the ref below points at it, and the request gives the repository's path.
$G update-ref "refs/oma/req/$PR" "$HEAD_SHA" 2>/dev/null || true
MYREPO=$(cd base && git rev-parse --absolute-git-dir 2>/dev/null || echo -)
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$PR" "$HEAD_SHA" "$FPATH" "$MODE" "$$" "$(printf '%s' "$MSG" | base64 -w0)" "$MYREPO" > "$Q/req/.$RID"
mv "$Q/req/.$RID" "$Q/req/$RID"
MAXCHAIN=${OMA_MAX_CHAIN:-60}

# The leader, holding the main lock: every live request in the spool (oldest first, at most MAXCHAIN) in one push.
lead() {
  local TRY REQS R P H F M PID B64 SRC MAIN TIP C TREE CHANGES RES OUT HEADS N=0 IDX="$PWD/gm_index_lead"
  find "$Q/res" -type f -mmin +30 -delete 2>/dev/null   # results nobody came back for
  for TRY in 1 2 3 4 5 6 7 8 9 10; do
    REQS=()
    for R in $(ls "$Q/req" 2>/dev/null | grep -v '^\.' | sort | head -n "$MAXCHAIN"); do
      IFS=$'\t' read -r P H F M PID B64 SRC < "$Q/req/$R" 2>/dev/null || { rm -f "$Q/req/$R"; continue; }
      kill -0 "$PID" 2>/dev/null || { rm -f "$Q/req/$R"; continue; }   # its slot gave up (timeout): not merged for it
      REQS+=("$R")
    done
    [ "${#REQS[@]}" -gt 0 ] || return 0
    # main and every head not here yet, in one fetch
    T0=$(date +%s.%N)
    HEADS=(); LOCAL=()
    for R in "${REQS[@]}"; do
      IFS=$'\t' read -r P H F M PID B64 SRC < "$Q/req/$R"
      $G cat-file -e "$H^{commit}" 2>/dev/null && continue
      HEADS+=("refs/pull/$P/head"); LOCAL+=("$P"$'\t'"${SRC:--}")
    done
    # One or two missing heads: take them from the requesting slots' repositories (local, under a second each). More:
    # one batched fetch from GitHub with main below (one round trip, a few seconds), since each local fetch packs out
    # of a 400 MB repository and they run one after another (measured: ~1 s per head, 10-21 s per chain).
    if [ "${#LOCAL[@]}" -le 2 ]; then
      HEADS=()
      for L in "${LOCAL[@]}"; do
        P=${L%%$'\t'*}; SRC=${L#*$'\t'}
        { [ "$SRC" != - ] && [ -d "$SRC" ] && $G fetch -q --no-tags --depth 1 "file://$SRC" "refs/oma/req/$P" 2>/dev/null; } || HEADS+=("refs/pull/$P/head")
      done
    fi
    $G fetch -q --no-tags --depth 1 origin "+refs/heads/main:refs/oma/main" "${HEADS[@]}" 2>/dev/null \
      || $G fetch -q --no-tags --depth 1 origin "+refs/heads/main:refs/oma/main" || { sleep 5; continue; }
    MAIN=$($G rev-parse refs/oma/main); TIP=$MAIN; T1=$(date +%s.%N)
    : > gm_results
    for R in "${REQS[@]}"; do
      IFS=$'\t' read -r P H F M PID B64 SRC < "$Q/req/$R"
      B=$($G rev-parse "$H:$F" 2>/dev/null) || { printf '%s\tALONE\t-\n' "$R" >> gm_results; continue; }
      if $G cat-file -e "$TIP:$F" 2>/dev/null; then
        [ "$M" = replace ] || { printf '%s\tRULE\talready on main\n' "$R" >> gm_results; continue; }
        $G show "$TIP:$F" > gm_old.lean; $G show "$B" > gm_new.lean
        read -r RES _ _ < <(python3 -I base/tools/prooflen.py gm_old.lean gm_new.lean)
        [ "$RES" = shorter ] || { printf '%s\tRULE\tnot shorter than the proof on main\n' "$R" >> gm_results; continue; }
      fi
      rm -f "$IDX"
      TREE=$(GIT_INDEX_FILE="$IDX" $G read-tree "$TIP" && GIT_INDEX_FILE="$IDX" $G update-index --add --cacheinfo "100644,$B,$F" && GIT_INDEX_FILE="$IDX" $G write-tree) \
        || { printf '%s\tALONE\t-\n' "$R" >> gm_results; continue; }
      CHANGES=$($G diff-tree -r --name-status "$TIP" "$TREE")
      [ "$CHANGES" = "$(printf 'A\t%s' "$F")" ] || [ "$CHANGES" = "$(printf 'M\t%s' "$F")" ] \
        || { printf '%s\tFAIL\tunexpected change\n' "$R" >> gm_results; continue; }
      C=$(printf '%s' "$B64" | base64 -d | $G "${ID[@]}" commit-tree "$TREE" -p "$TIP" -p "$H") || { printf '%s\tALONE\t-\n' "$R" >> gm_results; continue; }
      printf '%s\tOK\t%s\n' "$R" "$C" >> gm_results; TIP=$C
    done
    T2=$(date +%s.%N)
    if [ "$TIP" != "$MAIN" ]; then
      # push.negotiate: find what GitHub already has through the fetch protocol, which sees refs/pull/*, so the heads'
      # trees and blobs (already on GitHub) are not sent again; without it a chain of ten merges uploaded ten trees
      if OUT=$($G -c push.negotiate=true push -q origin "$TIP:refs/heads/main" 2>&1); then
        N=$(grep -c $'\tOK\t' gm_results)
        echo "group commit: $N merges in one push ($TIP) fetch=$(echo "$T1 - $T0" | bc)s build=$(echo "$T2 - $T1" | bc)s push=$(echo "$(date +%s.%N) - $T2" | bc)s" >&2
      elif printf '%s' "$OUT" | grep -qiE "$RACE"; then
        sleep 1; continue   # main moved (a push from elsewhere): the whole chain again on the new main
      else
        echo "group push refused: ${OUT:0:200}" >&2
        sed -i $'s/\tOK\t.*/\tALONE\t-/' gm_results   # every slot merges alone (and may fall back to one parent)
      fi
    fi
    while IFS=$'\t' read -r R S X; do
      printf '%s\t%s\n' "$S" "$X" > "$Q/res/.$R"; mv "$Q/res/.$R" "$Q/res/$R"; rm -f "$Q/req/$R"
    done < gm_results
    return 0
  done
  for R in "${REQS[@]}"; do printf 'ALONE\t-\n' > "$Q/res/.$R"; mv "$Q/res/.$R" "$Q/res/$R"; rm -f "$Q/req/$R"; done
}

for ROUND in 1 2 3 4 5 6 7 8 9 10 11 12; do
  flock -w 900 8 || { rm -f "$Q/req/$RID"; fail "main locked"; }
  [ -f "$Q/res/$RID" ] || lead
  flock -u 8
  if [ -f "$Q/res/$RID" ]; then
    IFS=$'\t' read -r S X < "$Q/res/$RID"; rm -f "$Q/res/$RID"
    case "$S" in
      OK) echo "$X"; exit 0 ;;
      RULE) fail "$X" 2 ;;
      FAIL) fail "$X" ;;
      *) merge_alone ;;
    esac
  fi
done
rm -f "$Q/req/$RID"; merge_alone

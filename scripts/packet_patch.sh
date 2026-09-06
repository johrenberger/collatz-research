#!/usr/bin/env bash
# Safe patch/worktree primitives for the external agent project workspace.
set -euo pipefail

usage() {
  echo "usage: $0 {snapshot|apply|worktree} PROJECT_ROOT ARG..." >&2
  exit 64
}

require_project() {
  PROJECT_ROOT=$1
  REPO="$PROJECT_ROOT/repo"
  test -d "$REPO/.git" || { echo "missing Git checkout: $REPO" >&2; exit 2; }
}

snapshot() {
  require_project "$1"
  PACKET_ID=$2
  test -n "$PACKET_ID" || usage
  mkdir -p "$PROJECT_ROOT/state/patches"
  PATCH="$PROJECT_ROOT/state/patches/${PACKET_ID}-$(date -u +%Y%m%dT%H%M%SZ).patch"
  git -C "$REPO" diff --binary > "$PATCH"
  printf '%s\n' "$PATCH"
}

apply_patch_file() {
  require_project "$1"
  PATCH=$2
  test -f "$PATCH" || { echo "missing patch: $PATCH" >&2; exit 2; }
  test -z "$(git -C "$REPO" status --porcelain)" || {
    echo "refusing to apply onto a dirty worktree; snapshot or commit first" >&2
    exit 3
  }
  git -C "$REPO" apply --3way --index "$PATCH"
}

new_worktree() {
  require_project "$1"
  PACKET_ID=$2
  BRANCH=$3
  test -n "$PACKET_ID" && test -n "$BRANCH" || usage
  TARGET="$PROJECT_ROOT/worktrees/$PACKET_ID"
  test ! -e "$TARGET" || { echo "worktree already exists: $TARGET" >&2; exit 3; }
  mkdir -p "$PROJECT_ROOT/worktrees"
  git -C "$REPO" worktree add -b "$BRANCH" "$TARGET" HEAD
}

test $# -ge 2 || usage
COMMAND=$1
shift
case "$COMMAND" in
  snapshot) test $# -eq 2 || usage; snapshot "$@" ;;
  apply) test $# -eq 2 || usage; apply_patch_file "$@" ;;
  worktree) test $# -eq 3 || usage; new_worktree "$@" ;;
  *) usage ;;
esac

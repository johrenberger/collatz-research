#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
openclaw_home="${OPENCLAW_HOME:-/data/.openclaw}"
workspace_root="${OPENCLAW_WORKSPACE:-$openclaw_home/workspace}"
mode="${1:-install}"

case "$mode" in
  install|--check) ;;
  *) echo "usage: $0 [install|--check]" >&2; exit 2 ;;
esac

failed=0
while IFS= read -r -d '' source_dir; do
  name="$(basename "$source_dir")"
  case "$name" in
    formal-math-*) target="$openclaw_home/skills/$name" ;;
    collatz-*) target="$workspace_root/skills/$name" ;;
    *) continue ;;
  esac

  mkdir -p "$(dirname "$target")"
  if [[ -L "$target" ]]; then
    existing="$(readlink -f "$target" || true)"
    expected="$(readlink -f "$source_dir")"
    if [[ "$existing" == "$expected" ]]; then
      echo "OK $target -> $source_dir"
      continue
    fi
    echo "Refusing to replace unexpected symlink: $target -> $(readlink "$target")" >&2
    failed=1
    continue
  fi

  if [[ -e "$target" ]]; then
    if ! diff -qr "$source_dir" "$target" >/dev/null; then
      echo "Refusing to replace runtime skill with differing contents: $target" >&2
      failed=1
      continue
    fi
    if [[ "$mode" == "--check" ]]; then
      echo "MISSING LINK $target (contents match; run installer)"
      failed=1
      continue
    fi
    rm -rf -- "$target"
  elif [[ "$mode" == "--check" ]]; then
    echo "MISSING $target" >&2
    failed=1
    continue
  fi

  ln -s "$source_dir" "$target"
  echo "LINKED $target -> $source_dir"
done < <(find "$repo_root/.openclaw/skills" -mindepth 1 -maxdepth 1 -type d -print0 | sort -z)

exit "$failed"

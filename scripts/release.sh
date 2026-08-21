#!/bin/bash
set -euo pipefail

usage() {
  cat <<EOF
Usage: $0 PACKAGE [--publish | --check-only]

PACKAGE must be microecta or microecta-generator.
Without an option, validates and uploads a package candidate.
--publish validates and publishes the release.
--check-only validates the exact artifacts without uploading them.
EOF
  exit "${1:-0}"
}

case "${1:-}" in
  -h|--help) usage 0 ;;
  "") usage 1 ;;
esac

package="$1"
shift

case "$package" in
  microecta|microecta-generator) ;;
  *) echo "Error: unknown package '$package'" >&2; usage 1 ;;
esac

publish=false
check_only=false
for arg in "$@"; do
  case "$arg" in
    --publish) publish=true ;;
    --check-only) check_only=true ;;
    -h|--help) usage 0 ;;
    *) echo "Error: unknown argument '$arg'" >&2; usage 1 ;;
  esac
done

if [[ "$publish" == true && "$check_only" == true ]]; then
  echo "Error: --publish and --check-only are mutually exclusive." >&2
  exit 1
fi

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

if [[ "$check_only" == false ]] && ! git diff --quiet --exit-code; then
  echo "Error: tracked worktree changes must be committed before upload." >&2
  exit 1
fi

if [[ "$check_only" == false ]] && ! git diff --cached --quiet --exit-code; then
  echo "Error: staged changes must be committed before upload." >&2
  exit 1
fi

version="$(awk '/^version:/ {print $2; exit}' "$package/$package.cabal")"
if [[ "$publish" == true ]] && grep -q "^## $version - Unreleased$" "$package/CHANGELOG.md"; then
  echo "Error: date the $version changelog entry before publishing." >&2
  exit 1
fi

shopt -s nullglob
release_build_dir="dist-newstyle/release/$package"
mkdir -p "$release_build_dir/sdist"
rm -f "$release_build_dir"/"$package"-[0-9]*-docs.tar.gz
rm -f "$release_build_dir"/sdist/"$package"-[0-9]*.tar.gz

echo "=== Checking $package-$version ==="
(
  cd "$package"
  cabal check
)
cabal test --builddir="$release_build_dir" "$package":unit-tests -O2 --ghc-options=-Werror --test-show-details=direct
cabal haddock --builddir="$release_build_dir" --haddock-for-hackage "lib:$package" --ghc-options=-Werror
cabal sdist --builddir="$release_build_dir" "$package"

sdists=("$release_build_dir"/sdist/"$package"-[0-9]*.tar.gz)
docs=("$release_build_dir"/"$package"-[0-9]*-docs.tar.gz)
if [[ ${#sdists[@]} -ne 1 || ${#docs[@]} -ne 1 ]]; then
  echo "Error: expected exactly one source archive and one documentation archive." >&2
  exit 1
fi

release_tmp="$(mktemp -d "${TMPDIR:-/tmp}/microecta-release.XXXXXX")"
trap 'rm -rf "$release_tmp"' EXIT
tar -xzf "${sdists[0]}" -C "$release_tmp"
(
  cd "$release_tmp/$package-$version"
  cabal test all -O2 --ghc-options=-Werror --test-show-details=direct
)

if [[ "$check_only" == true ]]; then
  echo "=== Validated: $package-$version ==="
  exit 0
fi

upload_args=()
if [[ "$publish" == true ]]; then
  upload_args+=(--publish)
fi

echo "=== Uploading $package-$version ==="
cabal upload "${upload_args[@]}" "${sdists[0]}"
cabal upload "${upload_args[@]}" --documentation "${docs[0]}"
echo "=== Done: $package-$version ==="

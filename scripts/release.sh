#!/bin/bash
set -euo pipefail

usage() {
  cat <<EOF
Usage: $0 PACKAGE [--publish | --check-only]

PACKAGE must be microecta, microecta-generator, microlta, or
microlta-generator.
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
  microecta|microecta-generator|microlta|microlta-generator) ;;
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
if [[ "$publish" == true && -f "$package/CHANGELOG.md" ]] \
  && grep -q "^## $version - Unreleased$" "$package/CHANGELOG.md"; then
  echo "Error: date the $version changelog entry before publishing." >&2
  exit 1
fi

shopt -s nullglob
release_build_dir="dist-newstyle/release/$package"
cabal clean --builddir="$release_build_dir"
mkdir -p "$release_build_dir/sdist"

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

case "$package" in
  microecta) dependencies=() ;;
  microecta-generator|microlta) dependencies=(microecta) ;;
  microlta-generator) dependencies=(microecta microecta-generator microlta) ;;
esac

if [[ ${#dependencies[@]} -gt 0 ]]; then
  project_packages=("$release_tmp/$package-$version")
  for dependency in "${dependencies[@]}"; do
    dependency_build_dir="$release_build_dir/dependencies/$dependency"
    mkdir -p "$dependency_build_dir/sdist"
    rm -f "$dependency_build_dir"/sdist/"$dependency"-[0-9]*.tar.gz
    cabal sdist --builddir="$dependency_build_dir" "$dependency"

    dependency_sdists=("$dependency_build_dir"/sdist/"$dependency"-[0-9]*.tar.gz)
    if [[ ${#dependency_sdists[@]} -ne 1 ]]; then
      echo "Error: expected exactly one $dependency source archive." >&2
      exit 1
    fi

    dependency_version="$(awk '/^version:/ {print $2; exit}' "$dependency/$dependency.cabal")"
    tar -xzf "${dependency_sdists[0]}" -C "$release_tmp"
    project_packages+=("$release_tmp/$dependency-$dependency_version")
  done

  {
    echo "packages:"
    printf '  %s\n' "${project_packages[@]}"
    echo
    echo "package *"
    echo "  optimization: False"
  } > "$release_tmp/cabal.project"

  (
    cd "$release_tmp"
    cabal test "$package":unit-tests -O2 --ghc-options=-Werror --test-show-details=direct
  )
else
  (
    cd "$release_tmp/$package-$version"
    cabal test all -O2 --ghc-options=-Werror --test-show-details=direct
  )
fi

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

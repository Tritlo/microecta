#!/bin/bash
set -euo pipefail

usage() {
  echo "Usage: $0 PACKAGE [--publish]"
  echo ""
  echo "PACKAGE must be microecta or microecta-generator."
  echo "Without --publish, uploads as a package candidate (dry run)."
  echo "With --publish, uploads as a published release."
  exit 1
}

if [[ $# -eq 0 ]]; then
  usage
fi

PACKAGE="$1"
shift

case "$PACKAGE" in
  microecta|microecta-generator) ;;
  *) echo "Error: unknown package '$PACKAGE'"; usage ;;
esac

publish_flag=""
for arg in "$@"; do
  case "$arg" in
    --publish) publish_flag="--publish" ;;
    -h|--help) usage ;;
    *) echo "Error: unknown argument '$arg'" ; usage ;;
  esac
done

# Clean previous artifacts
rm -rf dist-newstyle/"$PACKAGE"-[0-9]*-docs.tar.gz
rm -rf dist-newstyle/sdist/"$PACKAGE"-[0-9]*.tar.gz

# Build docs and the selected source distribution.
cabal haddock --haddock-for-hackage "lib:$PACKAGE"
cabal sdist "$PACKAGE"

# Credentials
read -p "Username: " username
read -sp "Password: " password
echo ""

echo ""
echo "=== Releasing $PACKAGE ==="

# Upload source tarball
cabal upload $publish_flag -u "$username" -p "$password" dist-newstyle/sdist/"$PACKAGE"-[0-9]*.tar.gz
# Upload docs
cabal upload $publish_flag -d -u "$username" -p "$password" dist-newstyle/"$PACKAGE"-[0-9]*-docs.tar.gz

echo "=== Done: $PACKAGE ==="

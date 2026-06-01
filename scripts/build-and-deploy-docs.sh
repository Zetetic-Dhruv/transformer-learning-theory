#!/usr/bin/env bash
#
# Build the doc-gen4 API documentation locally and deploy it to the gh-pages
# branch (served by GitHub Pages). Manual refresh: run this whenever you want
# the published docs to reflect the current source.
#
# Requirements:
#   - the local TorchLean (design-lab) checkout at the path in lakefile.lean,
#     since the Bridge/* modules depend on it (CI cannot build them);
#   - the `docbuild/` subpackage (doc-gen4 pinned to the toolchain).
#
# Usage:
#   scripts/build-and-deploy-docs.sh            # build + deploy
#   scripts/build-and-deploy-docs.sh --build    # build only, no deploy
#
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

echo ">> Resolving doc-gen4 (docbuild subpackage)…"
( cd docbuild && MATHLIB_NO_CACHE_ON_UPDATE=1 lake update >/dev/null )

echo ">> Building API documentation (doc-gen4)… this is heavy (full closure)."
( cd docbuild && lake build TLT_Proofs:docs )

DOC_OUT="$REPO_ROOT/docbuild/.lake/build/doc"
[ -d "$DOC_OUT" ] || { echo "ERROR: doc output not found at $DOC_OUT"; exit 1; }
echo ">> Docs generated at: $DOC_OUT"

if [ "${1:-}" = "--build" ]; then
  echo ">> --build given; skipping deploy."
  exit 0
fi

echo ">> Deploying to gh-pages (single orphan commit; force-replaced each refresh)…"
WORKTREE="$(mktemp -d)"
cleanup() { git worktree remove --force "$WORKTREE" >/dev/null 2>&1 || true; }
trap cleanup EXIT

git worktree add --detach "$WORKTREE" >/dev/null
(
  cd "$WORKTREE"
  git checkout --orphan gh-pages >/dev/null 2>&1
  git rm -rf . >/dev/null 2>&1 || true

  mkdir -p docs
  cp -r "$DOC_OUT/." docs/
  cp "$REPO_ROOT/docs/index.html" index.html
  touch .nojekyll            # doc-gen4 emits files beginning with "_"; bypass Jekyll

  git add -A
  git commit -m "Deploy docs ($(date -u +%Y-%m-%dT%H:%M:%SZ))" >/dev/null
  git push --force origin gh-pages
)

echo ">> Deployed. If GitHub Pages is not yet enabled, set Source = branch gh-pages, folder / (root)."

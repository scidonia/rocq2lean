#!/usr/bin/env bash
# Measure how much of a small, ordinary Rocq development carries.
#
# `examples/mini` is four files of the sort a user writes: syntax and an
# evaluator, a substitution function with a theorem, bounded arithmetic with a
# module, and an indexed vector. The script runs both halves of the pipeline:
#
#   statements  definitions, inductives, records, modules, theorem statements;
#               proofs are assumed. This must elaborate with no errors.
#   proofs      the same files with Rocq's kernel proof terms. The count of
#               Lean errors and the failing declarations are the measurement.
#
# Like the milestone scripts, this re-enters the dev shell. It reads the
# stdlib JSONs produced by `tests/compcert-a1.sh`; run that once first.
set -euo pipefail

if [ -z "${ROCQ2LEAN_DEV_SHELL:-}" ]; then
  exec nix develop -c "$0" "$@"
fi

cd "$(dirname "$0")/.."

WORK=build/mini
STDLIB="${ROCQPATH%%:*}/Stdlib"
EXTRACTOR=extractor/_build/default/bin/main.exe
TRANSLATOR=./.lake/build/bin/rocq2lean
FILES=(Syntax Subst Bounded Vec)

if [ ! -d build/compcert-a1/json ]; then
  echo "missing build/compcert-a1/json; run tests/compcert-a1.sh first" >&2
  exit 1
fi

say() { printf '\n== %s\n' "$*"; }

say "building extractor and translator"
dune build --root extractor
lake build rocq2lean >/dev/null

say "compiling the Rocq project"
rm -rf "$WORK"
mkdir -p "$WORK/stmt" "$WORK/full"
(
  cd examples/mini
  for f in "${FILES[@]}"; do
    rocq compile -R . Mini "$f.v"
  done
)

say "extracting statements and proof terms"
for f in "${FILES[@]}"; do
  "$EXTRACTOR" -R "$PWD/examples/mini" Mini -- \
    "$PWD/examples/mini/$f.v" "$WORK/stmt/$f.json" --no-proof-bodies
  "$EXTRACTOR" -R "$PWD/examples/mini" Mini -- \
    "$PWD/examples/mini/$f.v" "$WORK/full/$f.json"
done
# The mini project uses Nat lemmas from the stdlib. Their bodies are dropped,
# so the join turns them into marked assumptions; that is the compatibility
# boundary, not a failure of the mini project itself.
"$EXTRACTOR" -R "$STDLIB" Stdlib -- \
  "$STDLIB/Arith/PeanoNat.v" "$WORK/PeanoNat.json" --no-proof-bodies

statements() {
  local out="$WORK/statements.lean" log="$WORK/statements.log"
  "$TRANSLATOR" --join "$out" --root Mini. --statements-only --axiomatise-theorems \
    build/compcert-a1/json/*.json "$WORK/PeanoNat.json" "$WORK"/stmt/*.json >"$log" 2>&1
  local decls unresolved assumed errors
  decls="$(sed -n 's/^rocq2lean: \([0-9]*\) declaration.*/\1/p' "$log" | tail -1)"
  unresolved="$(grep -c '^  unresolved:' "$log" || true)"
  assumed="$(grep -c 'ROCQ2LEAN-ASSUMED' "$out" || true)"
  lake env lean -DmaxErrors=100000 "$out" >"$WORK/statements.out" 2>&1 || true
  errors="$(grep -c 'error' "$WORK/statements.out" || true)"
  echo "statements: $decls declarations, $unresolved unresolved, $assumed assumed, $errors Lean errors"
  [ "$unresolved" = 0 ] && [ "$errors" = 0 ]
}

proofs() {
  local out="$WORK/proofs.lean" log="$WORK/proofs.log"
  "$TRANSLATOR" --join "$out" --root Mini. \
    build/compcert-a1/json/*.json "$WORK/PeanoNat.json" "$WORK"/full/*.json >"$log" 2>&1
  local decls unresolved markers errors
  decls="$(sed -n 's/^rocq2lean: \([0-9]*\) declaration.*/\1/p' "$log" | tail -1)"
  unresolved="$(grep -c '^  unresolved:' "$log" || true)"
  markers="$(grep -c '^  untranslated:' "$log" || true)"
  lake env lean -DmaxErrors=100000 "$out" >"$WORK/proofs.out" 2>&1 || true
  errors="$(grep -c 'error' "$WORK/proofs.out" || true)"
  echo "proofs: $decls declarations, $unresolved unresolved, $markers markers, $errors Lean errors"
  echo "proof errors: $WORK/proofs.out"
}

say "statements and definitions"
if ! statements; then
  echo "FAIL: the statement-level translation did not elaborate" >&2
  exit 1
fi

say "proof terms"
proofs

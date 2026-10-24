#!/usr/bin/env bash
# End-to-end checks. Run from anywhere; the script re-enters the dev shell so
# the Rocq OCaml libraries and the pinned Lean are the ones the build uses.
set -euo pipefail

if [ -z "${ROCQ2LEAN_DEV_SHELL:-}" ]; then
  exec nix develop -c "$0" "$@"
fi

cd "$(dirname "$0")/.."
mkdir -p build

echo "== building extractor"
dune build --root extractor
EXTRACT=extractor/_build/default/bin/main.exe

echo "== building translator"
lake build rocq2lean

status=0

for source in tests/cases/*.v; do
  name="$(basename "$source" .v)"
  echo "== $name"
  "$EXTRACT" -- "$source" "build/$name.json"
  ./.lake/build/bin/rocq2lean "build/$name.json" "build/$name.lean"

  # Every case must elaborate. A marked, omitted declaration is allowed and is
  # checked below; a type error is not.
  if ! lake env lean "build/$name.lean" >"build/$name.out" 2>&1; then
    echo "FAIL: build/$name.lean did not elaborate"
    cat "build/$name.out"
    status=1
    continue
  fi

  # A translated proof must not smuggle in an axiom: `sorryAx` or any other
  # axiom defeats the point of carrying the proof term across.
  theorems="$(sed -n 's/^theorem \([^ :]*\).*/\1/p' "build/$name.lean")"
  if [ -n "$theorems" ]; then
    cp "build/$name.lean" "build/$name.axioms.lean"
    while read -r theorem; do
      [ -n "$theorem" ] && printf '#print axioms %s\n' "$theorem" >>"build/$name.axioms.lean"
    done <<<"$theorems"
    lake env lean "build/$name.axioms.lean" >"build/$name.axioms.out" 2>&1
    if grep -q 'depends on axioms' "build/$name.axioms.out" || grep -q 'sorryAx' "build/$name.axioms.out"; then
      echo "FAIL: a translated proof depends on an axiom"
      cat "build/$name.axioms.out"
      status=1
    fi
  fi

  # No `sorry` may appear unless it is a marked declaration body.
  if grep -q 'sorry' "build/$name.lean" && ! grep -q 'ROCQ2LEAN-UNTRANSLATED' "build/$name.lean"; then
    echo "FAIL: build/$name.lean has an unmarked sorry"
    status=1
  fi
done

# Markers are the contract with the reader: check the two cases that must have
# them, and that a fully translatable case has none.
check_marker() {
  if ! grep -q 'ROCQ2LEAN-UNTRANSLATED (' "build/$1.lean"; then
    echo "FAIL: build/$1.lean should carry an untranslated marker"
    status=1
  fi
}
check_clean() {
  if grep -q 'ROCQ2LEAN-UNTRANSLATED (' "build/$1.lean"; then
    echo "FAIL: build/$1.lean carries an unexpected marker"
    status=1
  fi
}
check_script() {
  if ! grep -q '^  intro ' "build/$1.lean" && ! grep -q '^  induction ' "build/$1.lean"; then
    echo "FAIL: build/$1.lean has no generated script"
    status=1
  fi
}
check_marker basic
check_marker poly
check_marker mutual
check_clean mutual-fix
check_marker propositions
check_marker option
check_marker untranslatable
check_marker coinductive
check_clean nat
check_clean records
check_clean section
check_clean primitive-record
check_clean imports
check_clean dependent
check_clean logic

check_has() {
  if ! grep -q "$2" "build/$1.lean"; then
    echo "FAIL: build/$1.lean does not contain '$2'"
    status=1
  fi
}
check_script basic
check_script poly
check_script nat
check_script records
check_script logic
check_has logic 'rcases'
check_has nat 'rw \['
check_has basic 'induction'
check_has nat 'intro n'

# Statements-only keeps definition bodies and admits proofs. If a definition
# were made opaque, every definitional equality across files would break.
./.lake/build/bin/rocq2lean "build/basic.json" "build/basic.statements.lean" --statements-only >/dev/null
if ! lake env lean "build/basic.statements.lean" >"build/basic.statements.out" 2>&1; then
  echo "FAIL: build/basic.statements.lean did not elaborate"
  cat "build/basic.statements.out"
  status=1
fi
if ! grep -A1 'def basic_pred2' "build/basic.statements.lean" | grep -q 'fun'; then
  echo "FAIL: statements-only made a definition opaque"
  status=1
fi
if ! grep -q 'theorem basic_plus2_O_r .* := by' "build/basic.statements.lean"; then
  echo "FAIL: statements-only did not admit a proof"
  status=1
fi

if [ "$status" -ne 0 ]; then
  echo "== FAILED"
  exit 1
fi
echo "== OK"

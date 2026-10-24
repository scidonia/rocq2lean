#!/usr/bin/env bash
# Reproduce milestone A2: CompCert's `common/AST.v` plus the declarations it
# actually uses from Errors, Integers, Floats, Flocq, Archi, String and
# SpecFloat must elaborate in Lean with no errors and no unresolved references.
#
# Proofs are still out of scope: AST's theorems are named assumptions. Seven
# decision procedures whose bodies need an explicit dependent `Case` motive are
# assumed as well; the generated file lists every assumption.
#
# This builds CompCert with its own Makefile (`configure` + `make`), which in
# turn needs `cpp` and `menhir` for `make depend`; `rocq dep` supplies the Coq
# dependencies. Run directly (it re-enters the dev shell) or via
# `nix develop -c`.
set -euo pipefail

if [ -z "${ROCQ2LEAN_DEV_SHELL:-}" ]; then
  exec nix develop -c "$0" "$@"
fi

cd "$(dirname "$0")/.."

WORK=build/compcert-a2
SRC="$WORK/src"
JSON="$WORK/json"
LEAN_OUT="$WORK/A2.lean"
EXTRACTOR=extractor/_build/default/bin/main.exe

say() { printf '\n== %s\n' "$*"; }

say "building extractor and translator"
dune build --root extractor
lake build rocq2lean >/dev/null

# A1 already extracted the stdlib closure and Coqlib/Maps; reuse it rather than
# repeating five minutes of work.
if [ ! -d build/compcert-a1/json ]; then
  say "running the A1 preparation"
  ./tests/compcert-a1.sh
fi

say "locating sources"
COMPCERT_SRC="${COMPCERT_SRC:-$(nix eval --raw nixpkgs#rocqPackages.compcert.src.outPath)}"
THEORIES="$ROCQ2LEAN_DEV_SHELL/lib/coq/theories"
STDLIB_ROOT="${ROCQPATH%%:*}"
STDLIB="$STDLIB_ROOT/Stdlib"
echo "compcert: $COMPCERT_SRC"

say "building CompCert up to common/AST.vo"
rm -rf "$WORK"
mkdir -p "$SRC" "$JSON"
cp -r "$COMPCERT_SRC/." "$SRC/"
chmod -R u+w "$SRC"
(cd "$SRC" && ./configure x86_64-linux >/dev/null)
# CompCert's Makefile still spells dependency generation as `coqdep`; Rocq 9
# renamed it to `rocq dep` and the flag spelling differs, so use the coqdep the
# environment provides (the dev shell appends the caller's PATH).
command -v coqdep >/dev/null || {
  echo "this harness needs coqdep (CompCert's Makefile)" >&2
  exit 1
}
(cd "$SRC" && make depend >/dev/null 2>&1)
(cd "$SRC" && make -j"$(nproc)" common/AST.vo >/dev/null)

# extract <prefix> <root> <relative path> <output>
extract() {
  "$PWD/$EXTRACTOR" -R "$2" "$1" -- "$2/$3" "$JSON/$4.json" --no-proof-bodies
}

CORE="Corelib"
STD="Stdlib"

say "extracting CompCert files"
CCINCLUDES=(
  -R "$SRC/lib" compcert.lib
  -R "$SRC/common" compcert.common
  -R "$SRC/x86_64" compcert.x86_64
  -R "$SRC/flocq" Flocq
)
extract_cc() {
  local rel="$1" out="$2"
  "$PWD/$EXTRACTOR" "${CCINCLUDES[@]}" -- "$SRC/$rel" "$JSON/$out.json" --no-proof-bodies
}
extract_cc "x86_64/Archi.v" Archi
extract_cc "common/Errors.v" Errors
extract_cc "lib/Integers.v" Integers
extract_cc "lib/Floats.v" Floats
extract_cc "lib/Zbits.v" Zbits
extract_cc "lib/IEEE754_extra.v" IEEE754_extra
extract_cc "common/AST.v" AST

say "extracting the stdlib and Flocq declarations AST mentions"
extract $CORE "$THEORIES" "Floats/SpecFloat.v" SpecFloat
extract $CORE "$THEORIES" "Floats/FloatClass.v" FloatClass
extract $CORE "$THEORIES" "BinNums/IntDef.v" IntDef
extract $STD "$STDLIB" "Strings/Ascii.v" Ascii
extract $STD "$STDLIB" "Strings/String.v" String
extract $STD "$STDLIB" "Logic/Eqdep_dec.v" Eqdep_dec
extract $STD "$STDLIB" "Bool/Bool.v" Bool

mkdir -p "$WORK/flocq"
for f in $(find "$SRC/flocq" -name '*.v' | sort); do
  rel=${f#"$SRC/flocq/"}
  name=$(echo "$rel" | sed 's|/|_|g; s|\.v$||')
  if ! "$PWD/$EXTRACTOR" -R "$SRC/flocq" Flocq -- "$f" "$WORK/flocq/$name.json" \
    --no-proof-bodies >"$WORK/flocq/$name.log" 2>&1; then
    # Flocq's proof-only Prop modules can trip an internal Rocq assertion when
    # processed as a library; they are not part of AST's closure.
    echo "skipping $rel (extractor failed)"
    rm -f "$WORK/flocq/$name.json"
  fi
done

say "joining and translating"
"./.lake/build/bin/rocq2lean" --join "$LEAN_OUT" --root compcert.common.AST \
  --axiomatise-prefix Stdlib.ZArith.ZArith_dec. \
  --axiomatise-prefix Stdlib.Bool.Bool.bool_dec \
  --axiomatise-prefix compcert.lib.Integers.Int.eq_dec \
  --axiomatise-prefix compcert.lib.Integers.Int64.eq_dec \
  --axiomatise-prefix compcert.lib.Integers.Ptrofs.eq_dec \
  --axiomatise-prefix compcert.common.AST.calling_convention_eq \
  --axiomatise-prefix compcert.common.AST.signature_eq \
  --axiomatise-prefix compcert.lib.IEEE754_extra.Beq_dec \
  --statements-only --axiomatise-theorems \
  build/compcert-a1/json/*.json \
  "$JSON/Archi.json" "$JSON/Errors.json" "$JSON/Integers.json" "$JSON/Floats.json" \
  "$JSON/Zbits.json" "$JSON/IEEE754_extra.json" "$JSON/AST.json" \
  "$JSON/SpecFloat.json" "$JSON/FloatClass.json" "$JSON/IntDef.json" \
  "$JSON/Ascii.json" "$JSON/String.json" "$JSON/Eqdep_dec.json" "$JSON/Bool.json" \
  "$WORK"/flocq/*.json >"$WORK/translate.log" 2>&1

say "elaborating $LEAN_OUT"
if ! lake env lean -DmaxErrors=100000 "$LEAN_OUT" >"$WORK/lean.log" 2>&1; then
  echo "FAIL: Lean rejected the A2 unit" >&2
  grep -m 20 'error' "$WORK/lean.log" >&2 || true
  exit 1
fi

unresolved=$(grep -c '^  unresolved' "$WORK/translate.log" || true)
errors=$(grep -c 'error' "$WORK/lean.log" || true)
decls=$(grep -m1 -E '^rocq2lean: [0-9]+ declaration' "$WORK/translate.log" | sed -E 's/rocq2lean: ([0-9]+).*/\1/')
assumed=$(grep -c 'ROCQ2LEAN-ASSUMED' "$LEAN_OUT" || true)
printf '\nA2: %s declarations, %s assumed, %s unresolved, %s Lean errors\n' \
  "$decls" "$assumed" "$unresolved" "$errors"

if [ "$unresolved" -ne 0 ] || [ "$errors" -ne 0 ]; then
  echo "FAIL" >&2
  exit 1
fi
echo "A2 OK"

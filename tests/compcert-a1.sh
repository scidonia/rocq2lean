#!/usr/bin/env bash
# Reproduce milestone A1: CompCert's `lib/Coqlib.v` and `lib/Maps.v`, joined
# with the stdlib declarations they use, must elaborate in Lean with no errors
# and no unresolved references.
#
# Proofs are out of scope at this stage: CompCert's theorems are emitted as
# named assumptions (`ROCQ2LEAN-ASSUMED`), while definitions keep their bodies.
# Six CompCert definitions whose bodies need an explicit dependent `Case` motive
# and three `ZArith_dec` decision functions are assumed too; the script prints
# the full trusted list in the generated file.
#
# Run directly (it re-enters the dev shell) or via `nix develop -c`.
set -euo pipefail

if [ -z "${ROCQ2LEAN_DEV_SHELL:-}" ]; then
  exec nix develop -c "$0" "$@"
fi

cd "$(dirname "$0")/.."

WORK=build/compcert-a1
SRC="$WORK/src"
JSON="$WORK/json"
LEAN_OUT="$WORK/A1.lean"
EXTRACTOR=extractor/_build/default/bin/main.exe

say() { printf '\n== %s\n' "$*"; }

say "locating CompCert and Rocq libraries"
COMPCERT_SRC="${COMPCERT_SRC:-$(nix eval --raw nixpkgs#rocqPackages.compcert.src.outPath)}"
THEORIES="$ROCQ2LEAN_DEV_SHELL/lib/coq/theories"
STDLIB_ROOT="${ROCQPATH%%:*}"
STDLIB="$STDLIB_ROOT/Stdlib"
for p in "$COMPCERT_SRC" "$THEORIES" "$STDLIB"; do
  [ -e "$p" ] || {
    echo "missing: $p" >&2
    exit 1
  }
done
echo "compcert: $COMPCERT_SRC"
echo "corelib:  $THEORIES"
echo "stdlib:   $STDLIB"

say "building extractor and translator"
dune build --root extractor
lake build rocq2lean >/dev/null

say "preparing a writable CompCert tree"
rm -rf "$WORK"
mkdir -p "$SRC" "$JSON"
cp -r "$COMPCERT_SRC/." "$SRC/"
chmod -R u+w "$SRC"
(cd "$SRC" && rocq compile -R lib compcert.lib lib/Coqlib.v)
(cd "$SRC" && rocq compile -R lib compcert.lib lib/Maps.v)

# extract <prefix> <root> <relative path> <output>
extract() {
  "$PWD/$EXTRACTOR" -R "$2" "$1" -- "$2/$3" "$JSON/$4.json" --no-proof-bodies
}

say "extracting the stdlib closure"
extract Corelib "$THEORIES" "Numbers/BinNums.v" BinNums
extract Corelib "$THEORIES" "BinNums/PosDef.v" PosDef
extract Corelib "$THEORIES" "Lists/ListDef.v" ListDef
extract Corelib "$THEORIES" "Classes/RelationClasses.v" RelationClasses
extract Corelib "$THEORIES" "Classes/Equivalence.v" Equivalence
extract Corelib "$THEORIES" "Relations/Relation_Definitions.v" Relation_Definitions
extract Corelib "$THEORIES" "Classes/Morphisms.v" Morphisms
extract Stdlib "$STDLIB" "PArith/BinPosDef.v" BinPosDef
extract Stdlib "$STDLIB" "PArith/BinPos.v" BinPos
extract Stdlib "$STDLIB" "NArith/BinNatDef.v" BinNatDef
extract Stdlib "$STDLIB" "NArith/BinNat.v" BinNat
extract Stdlib "$STDLIB" "ZArith/BinIntDef.v" BinIntDef
extract Stdlib "$STDLIB" "ZArith/BinInt.v" BinInt
extract Stdlib "$STDLIB" "Lists/List.v" List
extract Stdlib "$STDLIB" "Classes/EquivDec.v" EquivDec
extract Stdlib "$STDLIB" "ZArith/Zpower.v" Zpower
extract Stdlib "$STDLIB" "ZArith/ZArith_dec.v" ZArith_dec

say "extracting Coqlib and Maps"
extract compcert.lib "$SRC/lib" "Coqlib.v" Coqlib
extract compcert.lib "$SRC/lib" "Maps.v" Maps

say "joining and translating"
"./.lake/build/bin/rocq2lean" --join "$LEAN_OUT" --root compcert.lib. \
  --axiomatise-prefix Stdlib.ZArith.ZArith_dec. \
  --axiomatise-prefix compcert.lib.Coqlib.option_eq \
  --axiomatise-prefix compcert.lib.Coqlib.list_norepet_dec \
  --axiomatise-prefix compcert.lib.Maps.PTree.tree_ind \
  --axiomatise-prefix compcert.lib.Maps.PTree_Properties.Equal_dec \
  --axiomatise-prefix compcert.lib.Maps.PTree_Properties.fold_ind \
  --statements-only --axiomatise-theorems \
  "$JSON/BinNums.json" "$JSON/PosDef.json" "$JSON/BinPosDef.json" \
  "$JSON/BinPos.json" "$JSON/BinNatDef.json" "$JSON/BinNat.json" \
  "$JSON/BinIntDef.json" "$JSON/BinInt.json" "$JSON/ListDef.json" \
  "$JSON/List.json" "$JSON/RelationClasses.json" "$JSON/Equivalence.json" \
  "$JSON/EquivDec.json" "$JSON/Relation_Definitions.json" \
  "$JSON/Morphisms.json" "$JSON/Zpower.json" "$JSON/ZArith_dec.json" \
  "$JSON/Coqlib.json" "$JSON/Maps.json" >"$WORK/translate.log" 2>&1

say "elaborating $LEAN_OUT"
if ! lake env lean -DmaxErrors=100000 "$LEAN_OUT" >"$WORK/lean.log" 2>&1; then
  echo "FAIL: Lean rejected the A1 unit" >&2
  grep -m 20 'error' "$WORK/lean.log" >&2 || true
  exit 1
fi

unresolved=$(grep -c '^  unresolved' "$WORK/translate.log" || true)
errors=$(grep -c 'error' "$WORK/lean.log" || true)
decls=$(grep -m1 -E '^rocq2lean: [0-9]+ declaration' "$WORK/translate.log" | sed -E 's/rocq2lean: ([0-9]+).*/\1/')
assumed=$(grep -c 'ROCQ2LEAN-ASSUMED' "$LEAN_OUT" || true)
printf '\nA1: %s declarations, %s assumed, %s unresolved, %s Lean errors\n' \
  "$decls" "$assumed" "$unresolved" "$errors"

if [ "$unresolved" -ne 0 ] || [ "$errors" -ne 0 ]; then
  echo "FAIL" >&2
  exit 1
fi
echo "A1 OK"

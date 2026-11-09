#!/usr/bin/env bash
# Full build + hygiene + axiom check of the Semialgebraic library.
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/env.sh
echo "== build =="
lake build Semialgebraic SemialgebraicCheck 2>&1 | grep -v '^trace\|Fetched\|✔\|Replayed' | tail -5
echo "== hygiene: sorry / admit / axiom / native_decide / unsafe =="
pat='\b(sorry|admit|native_decide)\b|^\s*(private\s+|protected\s+)?(axiom|unsafe)\b'
skip='`[^`]*(sorry|admit|native_decide|axiom|unsafe)|^[^:]+:[0-9]+:\s*(--|/-|\*)'
if grep -rnE "$pat" Semialgebraic Semialgebraic.lean SemialgebraicCheck | grep -vE "$skip" | grep -q .; then
  grep -rnE "$pat" Semialgebraic Semialgebraic.lean SemialgebraicCheck | grep -vE "$skip"
  echo "FAIL: forbidden token"; exit 1
fi
echo "none"
echo "== axioms of the interface theorems =="
out="$(mktemp)"
lake env lean scripts/CheckAxioms.lean | tee "$out"
if grep -vE "depends on axioms: \[propext, Classical.choice, Quot.sound\]|^$" "$out" | grep -q .; then
  echo "FAIL: unexpected axiom or error"; exit 1
fi
[ -s "$out" ] || { echo "FAIL: no axiom output"; exit 1; }
echo "OK: every interface theorem depends only on propext, Classical.choice, Quot.sound"

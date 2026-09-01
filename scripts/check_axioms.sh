#!/bin/sh
# Verify that the Solution theorems depend only on the three permitted axioms:
#   propext, Classical.choice, Quot.sound
set -eu
cd "$(dirname "$0")/.."

OUT="$(printf 'import Solution\n#print axioms MasonFlats.mason_log_concave_false\n' \
  | lake env lean --stdin 2>&1)" || {
  echo "$OUT"
  echo "FAIL: could not elaborate the probe (build first: lake build)"
  exit 1
}
echo "$OUT"

LINE="$(echo "$OUT" | grep "'MasonFlats.mason_log_concave_false' depends on axioms" || true)"
if [ -z "$LINE" ]; then
  echo "FAIL: no axiom report for MasonFlats.mason_log_concave_false"
  exit 1
fi
BAD="$(echo "$LINE" | sed -e "s/.*axioms: \\[//" -e "s/\\]//" -e "s/,/\\n/g" \
  | tr -d ' ' | grep -v -E '^(propext|Classical\.choice|Quot\.sound)$' || true)"
if [ -n "$BAD" ]; then
  echo "FAIL: MasonFlats.mason_log_concave_false depends on non-permitted axioms: $BAD"
  exit 1
fi
echo "OK: mason_log_concave_false depends only on permitted axioms."

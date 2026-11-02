#!/usr/bin/env bash
# Verifica el repo: Lean 4.35.0 + Mathlib v4.35.0, y el puente al corpus.
# CORPUS es un checkout de nava-robertson-schrodinger sobre Lean 4.35 (por defecto, ../nrs_corpus_435).
set -e
HERE=$(cd "$(dirname "$0")/.." && pwd)
CORPUS=${CORPUS:-$HERE/../nrs_corpus_435}
echo "== nrs3-hidrogeno"
(cd "$HERE" && lake build 2>&1 | grep -v "module system\|^⚠\|^✔\|^info" | tail -2)
echo "== puente al corpus"
(cd "$CORPUS" && lake build NavaRobertsonCertificados.D50k_WordDefectBand 2>&1 | tail -1 \
  && lake env lean "$HERE/Puente/D50g.lean" 2>&1 | grep -v "module system")
echo "OK (sin salida de error arriba = todo verde)"

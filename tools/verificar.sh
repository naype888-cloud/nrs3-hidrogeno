#!/usr/bin/env bash
# Verifica todo con la pila unificada (Lean 4.35.0, Mathlib v4.35.0, Physlib local con cache oficial).
set -e
R=/home/nava/lean-math
echo "== PR LatticeModels (physlib_wt_lattice)"
(cd $R/physlib_wt_lattice && lake build PhyslibAlpha.CondensedMatter.LatticeModels.BoxGraph 2>&1 | tail -1)
echo "== nrs3-hidrogeno"
(cd $R/nrs3-hidrogeno && lake build NRS3Hidrogeno 2>&1 | grep -v "module system\|^⚠\|^✔\|^info" | tail -2)
echo "== puentes al corpus (nrs_corpus_435)"
(cd $R/nrs_corpus_435 && lake build NavaRobertsonCertificados.D50k_WordDefectBand 2>&1 | tail -1 \
  && lake env lean $R/nrs3-hidrogeno/Puente/D50g.lean 2>&1 | grep -v "module system" ; \
  lake env lean $R/nrs3-hidrogeno/Puente/Caja.lean 2>&1 | grep -v "module system")
echo "OK (sin salida de error arriba = todo verde)"

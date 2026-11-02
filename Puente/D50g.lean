import NavaRobertsonCertificados.D50k_WordDefectBand
import NavaRobertsonCertificados.D50_ProperTimeSurplus
import NavaRobertsonIndependent.Mathematics.D8_Szego
import NavaRobertsonIndependent.Mathematics.D21_ElementalNRSInequality

/-!
# Bridge: the diagonals of the hydrogen cube cost the defects of `D50g`

Not a library of `nrs3-hidrogeno`: it is compiled inside the corpus
(`cd nava-robertson-schrodinger && lake env lean ../nrs3-hidrogeno/Puente/D50g.lean`), because the
corpus and the mosaic do not share a Mathlib.

The three spatial axes `x, y, z` each carry the Hilbert space `H_d` (`d` is the Hilbert `d`; this
file does not say what fixes it). An axis step is a letter of `Fin 3`; a diagonal is a word. At the
maximal current state of the three axes, every letter costs `defectGram d` (`D20`), so a word costs
its length times that: `2` for a face diagonal, `3` for a body diagonal. The cost is `0` exactly
for `d = 2, 3` and positive from `d = 4` (`D50`, `D20`), which is where `C_N(d) > 1` (`D8`).
-/

open WordDefect WordDefectBand TransportPosition NearMaxTension GramStep PathGraph3DNRS ProperTimeAxis GroupVelocity VelocityBand

namespace Puente

lemma wordDefect_const (g : ℝ) (w : List (Fin 3)) :
    wordDefect (fun _ => g) w = (w.length : ℝ) * g := by
  induction w with
  | nil => simp
  | cons a w ih => rw [wordDefect_cons, ih]; simp; ring

lemma cubeGram_const (d : ℕ) : cubeGram d d d = fun _ => defectGram d := by
  funext k; fin_cases k <;> simp [cubeGram]

/-- **At maximal tension on the three axes, a word costs its length times `defectGram d`.** -/
theorem word_cost {d : ℕ} (hd : 2 ≤ d) {Φ : H3D d d d} (hΦ : ‖Φ‖ = 1)
    (tx : tensionG (TX d d d) (PX d d d) Φ = 2 / ((d : ℝ) - 1))
    (ty : tensionG (TY d d d) (PY d d d) Φ = 2 / ((d : ℝ) - 1))
    (tz : tensionG (TZ d d d) (PZ d d d) Φ = 2 / ((d : ℝ) - 1)) (w : List (Fin 3)) :
    wordDefect (cubeDefect d d d Φ) w = (w.length : ℝ) * defectGram d := by
  rw [wordDefect_eq_of_maxTension hd hd hd hΦ tx ty tz w, cubeGram_const, wordDefect_const]

/-- A face diagonal costs two defects, a body diagonal three. -/
theorem face_body_cost {d : ℕ} (hd : 2 ≤ d) {Φ : H3D d d d} (hΦ : ‖Φ‖ = 1)
    (tx : tensionG (TX d d d) (PX d d d) Φ = 2 / ((d : ℝ) - 1))
    (ty : tensionG (TY d d d) (PY d d d) Φ = 2 / ((d : ℝ) - 1))
    (tz : tensionG (TZ d d d) (PZ d d d) Φ = 2 / ((d : ℝ) - 1)) :
    wordDefect (cubeDefect d d d Φ) [0, 1] = 2 * defectGram d ∧
      wordDefect (cubeDefect d d d Φ) [0, 1, 2] = 3 * defectGram d := by
  constructor
  · rw [word_cost hd hΦ tx ty tz]; norm_num
  · rw [word_cost hd hΦ tx ty tz]; norm_num

/-- **Every non-empty word costs a positive time from `d = 4` on**, and the same bound holds for
the `2` orders of a face diagonal and the `3! = 6` of a body diagonal. -/
theorem word_cost_pos {d : ℕ} (hd : 4 ≤ d) {Φ : H3D d d d} (hΦ : ‖Φ‖ = 1)
    (tx : tensionG (TX d d d) (PX d d d) Φ = 2 / ((d : ℝ) - 1))
    (ty : tensionG (TY d d d) (PY d d d) Φ = 2 / ((d : ℝ) - 1))
    (tz : tensionG (TZ d d d) (PZ d d d) Φ = 2 / ((d : ℝ) - 1)) {w : List (Fin 3)}
    (hw : w ≠ []) : 0 < wordDefect (cubeDefect d d d Φ) w := by
  rw [word_cost (by omega) hΦ tx ty tz]
  have : 0 < (w.length : ℝ) := by exact_mod_cast List.length_pos_iff.mpr hw
  exact mul_pos this (gramStep_gram_pos hd)

/-- **`defectGram d` in terms of `δ(d) = C_N(d) - 1` (`D8`).** -/
theorem defectGram_eq_gap {d : ℕ} (hd : 2 ≤ d) :
    defectGram d = Gnomon.geometricGap d * (2 + Gnomon.geometricGap d) / ((d : ℝ) - 1) ^ 2 := by
  rw [gramStep_gram hd, NRSInequality.CoherenceConstantSq_eq_sq hd]
  ring

/-- **A word costs `length · δ(2 + δ) / (d - 1)²`** at maximal tension on the three axes. -/
theorem word_cost_gap {d : ℕ} (hd : 2 ≤ d) {Φ : H3D d d d} (hΦ : ‖Φ‖ = 1)
    (tx : tensionG (TX d d d) (PX d d d) Φ = 2 / ((d : ℝ) - 1))
    (ty : tensionG (TY d d d) (PY d d d) Φ = 2 / ((d : ℝ) - 1))
    (tz : tensionG (TZ d d d) (PZ d d d) Φ = 2 / ((d : ℝ) - 1)) (w : List (Fin 3)) :
    wordDefect (cubeDefect d d d Φ) w =
      (w.length : ℝ) * (Gnomon.geometricGap d * (2 + Gnomon.geometricGap d) / ((d : ℝ) - 1) ^ 2) := by
  rw [word_cost hd hΦ tx ty tz w, defectGram_eq_gap hd]

end Puente

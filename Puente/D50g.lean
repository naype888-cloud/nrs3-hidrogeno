import NavaRobertsonCertificados.D50k_WordDefectBand
import NavaRobertsonCertificados.D50_ProperTimeSurplus
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import NavaRobertsonIndependent.Mathematics.D8_Szego
import NavaRobertsonIndependent.Mathematics.D21_ElementalNRSInequality

/-!
# Bridge: the hopping of the hydrogen cube and the cost of its diagonals (`D37`, `D50g`)

Not a library of `nrs3-hidrogeno`: it is compiled inside the corpus
(`cd nava-robertson-schrodinger && lake env lean ../nrs3-hidrogeno/Puente/D50g.lean`), because the
corpus and the mosaic do not share a Mathlib.

The three spatial axes `x, y, z` each carry the Hilbert space `H_d` (`d` is the Hilbert `d`; this
file does not say what fixes it). An axis step is a letter of `Fin 3`; a diagonal is a word. At the
maximal current state of the three axes, every letter costs `defectGram d` (`D20`), so a word costs
its length times that: `2` for a face diagonal, `3` for a body diagonal. The cost is `0` exactly
for `d = 2, 3` and positive from `d = 4` (`D50`, `D20`), which is where `C_N(d) > 1` (`D8`).
-/

open SimpleGraph WordDefect WordDefectBand TransportPosition NearMaxTension GramStep PathGraph3DNRS ProperTimeAxis GroupVelocity VelocityBand

namespace Puente

/-! ## The hopping of the cube is `ρ_x T_x + ρ_y T_y + ρ_z T_z`

The graph of the cube of `PhyslibAlpha.CondensedMatter.LatticeModels.BoxGraph` is the box product
of three paths; its adjacency operator is the sum over the axes of the hop of the path,
`A_d = ρ_d T_d` (`D3`), lifted to the axis (`D37`). -/

open Classical in
/-- **The adjacency operator of the cube graph is `ρ_x T_x + ρ_y T_y + ρ_z T_z`.** -/
theorem adjacency_cube {dx dy dz : ℕ} (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    Matrix.toEuclideanLin
        ((pathGraph dx □ (pathGraph dy □ pathGraph dz)).adjMatrix ℂ) =
      (rho dx : ℂ) • TX (dx := dx) (dy := dy) (dz := dz) +
        (rho dy : ℂ) • TY (dx := dx) (dy := dy) (dz := dz) +
        (rho dz : ℂ) • TZ (dx := dx) (dy := dy) (dz := dz) := by
  have hρ : ∀ d : ℕ, 2 ≤ d → (rho d : ℂ) ≠ 0 := by
    intro d hd
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have h1 : 0 < Real.cos (Real.pi / ((d : ℝ) + 1)) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · have : 0 < Real.pi / ((d : ℝ) + 1) := by positivity
        have := Real.pi_pos
        linarith
      · rw [div_lt_iff₀ (by positivity)]
        nlinarith [Real.pi_pos]
    have : rho d ≠ 0 := by unfold rho; positivity
    exact_mod_cast this
  have hM : (pathGraph dx □ (pathGraph dy □ pathGraph dz)).adjMatrix ℂ =
      (rho dx : ℂ) • liftAlong (eX dx dy dz) (Td dx) +
        (rho dy : ℂ) • liftAlong (eY dx dy dz) (Td dy) +
        (rho dz : ℂ) • liftAlong (eZ dx dy dz) (Td dz) := by
    have hT : ∀ d : ℕ, 2 ≤ d → ∀ i j : Fin d, (rho d : ℂ) * Td d i j = Ad d i j := by
      intro d hd i j
      have := hρ d hd
      unfold Td
      field_simp
    ext ⟨x, y, z⟩ ⟨x', y', z'⟩
    simp only [Matrix.add_apply, Matrix.smul_apply, liftAlong, Matrix.of_apply, eX, eY, eZ,
      Equiv.refl_apply, Equiv.coe_fn_mk, smul_eq_mul, ← mul_assoc, hT dx hx, hT dy hy, hT dz hz,
      Ad, MinStep, SimpleGraph.adjMatrix_apply, SimpleGraph.boxProd_adj, pathGraph_adj,
      Prod.mk.injEq]
    by_cases a1 : x = x' <;> by_cases a2 : y = y' <;> by_cases a3 : z = z' <;> simp_all
  simp only [TX, TY, TZ, ← map_smul, ← map_add, hM]

open Classical in
/-- **The hop form of the cube is `⟨ψ, (ρ_x T_x + ρ_y T_y + ρ_z T_z) ψ⟩`.** For a real `f` on the
cube, `Σ_{s,t} [s ~ t] f(s) f(t)` is the real part of that inner product. With
`NRS3Hidrogeno.adjForm_boxSet`, the hop form of the integer cube of `nrs3-hidrogeno` is the
quadratic form of the transport `T_d` of each axis (`D37`). -/
theorem form_cube {dx dy dz : ℕ} (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz)
    (f : Fin dx × Fin dy × Fin dz → ℝ) :
    ∑ s : Fin dx × Fin dy × Fin dz, ∑ t : Fin dx × Fin dy × Fin dz,
        (if (pathGraph dx □ (pathGraph dy □ pathGraph dz)).Adj s t then (1 : ℝ) else 0) *
          (f s * f t) =
      (inner ℂ (WithLp.toLp 2 (fun s => (f s : ℂ)) : EuclideanSpace ℂ (Fin dx × Fin dy × Fin dz))
        (((rho dx : ℂ) • TX (dx := dx) (dy := dy) (dz := dz) +
            (rho dy : ℂ) • TY (dx := dx) (dy := dy) (dz := dz) +
            (rho dz : ℂ) • TZ (dx := dx) (dy := dy) (dz := dz))
          (WithLp.toLp 2 (fun s => (f s : ℂ))))).re := by
  rw [← adjacency_cube hx hy hz]
  have h : inner ℂ (WithLp.toLp 2 (fun s => (f s : ℂ)) :
        EuclideanSpace ℂ (Fin dx × Fin dy × Fin dz))
      (Matrix.toEuclideanLin ((pathGraph dx □ (pathGraph dy □ pathGraph dz)).adjMatrix ℂ)
        (WithLp.toLp 2 (fun s => (f s : ℂ)))) =
      ((∑ s : Fin dx × Fin dy × Fin dz, ∑ t : Fin dx × Fin dy × Fin dz,
        (if (pathGraph dx □ (pathGraph dy □ pathGraph dz)).Adj s t then (1 : ℝ) else 0) *
          (f s * f t) : ℝ) : ℂ) := by
    simp [PiLp.inner_apply, Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> simp [mul_comm]
  rw [h, Complex.ofReal_re]

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

/-! ## The visible hypotheses: what the step is in seconds

Nothing below is derived. A physical step is given by three hypotheses, listed as fields: the cell
side `a`, the speed of light `c`, and the resolution floor `ℓ_P ≤ a` (Planck length as the limit of
resolution, with no extra factor: Mead 1964, Garay 1995; the factor `y` of the old SBPK
calibration is not used). The duration of a step is `a / c`. -/

/-- A physical step of the cube: the hypotheses that turn the dimensionless defect into time. -/
structure PhysicalStep where
  /-- Side of a cell. -/
  a : ℝ
  /-- The `c` of the system: the speed of the maximal current state (`|v| = 1` in the units of
  `D38`). For the system we live in it is the speed of light in vacuum; the same formula applied to
  the electron alone would give its own `c`, `ħ / (m a)` (`Escala.lean`). -/
  c : ℝ
  /-- Planck length. -/
  lP : ℝ
  c_pos : 0 < c
  lP_pos : 0 < lP
  /-- The Planck length is the floor of the resolution: a cell is not smaller. -/
  resolution : lP ≤ a

/-- A step lasts `a / c`. -/
noncomputable def PhysicalStep.duration (P : PhysicalStep) : ℝ := P.a / P.c

/-- The delay of a word of `D50g`, in seconds: its defect times the duration of a step. -/
noncomputable def PhysicalStep.delay (P : PhysicalStep) (defect : ℝ) : ℝ := defect * P.duration

lemma PhysicalStep.duration_ge (P : PhysicalStep) : P.lP / P.c ≤ P.duration :=
  div_le_div_of_nonneg_right P.resolution P.c_pos.le

/-- **The delay of a diagonal has the floor `defect · ℓ_P / c`** (`defect · t_P`), whatever the
cell. -/
theorem PhysicalStep.delay_ge (P : PhysicalStep) {g : ℝ} (hg : 0 ≤ g) :
    g * (P.lP / P.c) ≤ P.delay g :=
  mul_le_mul_of_nonneg_left P.duration_ge hg

/-- **The bridge, in seconds.** From `d = 4` on, at maximal tension, every non-empty word of the
cube has a delay of at least `defectGram d · t_P` per letter, under the hypotheses of `PhysicalStep`. -/
theorem word_delay_pos {d : ℕ} (hd : 4 ≤ d) {Φ : H3D d d d} (hΦ : ‖Φ‖ = 1)
    (tx : tensionG (TX d d d) (PX d d d) Φ = 2 / ((d : ℝ) - 1))
    (ty : tensionG (TY d d d) (PY d d d) Φ = 2 / ((d : ℝ) - 1))
    (tz : tensionG (TZ d d d) (PZ d d d) Φ = 2 / ((d : ℝ) - 1)) (P : PhysicalStep)
    {w : List (Fin 3)} (hw : w ≠ []) :
    (w.length : ℝ) * defectGram d * (P.lP / P.c) ≤ P.delay (wordDefect (cubeDefect d d d Φ) w) ∧
      0 < P.delay (wordDefect (cubeDefect d d d Φ) w) := by
  have hpos := word_cost_pos hd hΦ tx ty tz hw
  have hc := word_cost (by omega) hΦ tx ty tz w
  have hg : 0 < defectGram d := gramStep_gram_pos hd
  refine ⟨?_, mul_pos hpos (div_pos (P.lP_pos.trans_le P.resolution) P.c_pos)⟩
  have := P.delay_ge hpos.le
  rw [hc] at this ⊢
  linarith [this]

/-! ## One statement

The hopping of the cube and the words of `D50g` are the same three letters: the operator whose
words are costed is the adjacency of the cube graph, and at maximal tension on the three axes each
letter costs `defectGram d`. -/

open Classical in
/-- **The cube, in one statement.** For `d ≥ 2` and a unit state of maximal tension on the three
axes: the adjacency of the cube graph of side `d` is `ρ_d (T_x + T_y + T_z)`, and a word of
length `n` in these hops costs `n · defectGram d`, which is `0` for `d = 2, 3` and positive for
`d ≥ 4` (non-empty word). -/
theorem cube_hopping_and_cost {d : ℕ} (hd : 2 ≤ d) {Φ : H3D d d d} (hΦ : ‖Φ‖ = 1)
    (tx : tensionG (TX d d d) (PX d d d) Φ = 2 / ((d : ℝ) - 1))
    (ty : tensionG (TY d d d) (PY d d d) Φ = 2 / ((d : ℝ) - 1))
    (tz : tensionG (TZ d d d) (PZ d d d) Φ = 2 / ((d : ℝ) - 1)) :
    Matrix.toEuclideanLin ((pathGraph d □ (pathGraph d □ pathGraph d)).adjMatrix ℂ) =
        (rho d : ℂ) • (TX d d d + TY d d d + TZ d d d) ∧
      (∀ w : List (Fin 3),
        wordDefect (cubeDefect d d d Φ) w = (w.length : ℝ) * defectGram d) ∧
      (4 ≤ d → ∀ {w : List (Fin 3)}, w ≠ [] → 0 < wordDefect (cubeDefect d d d Φ) w) := by
  refine ⟨?_, fun w => word_cost hd hΦ tx ty tz w, fun h4 w hw => word_cost_pos h4 hΦ tx ty tz hw⟩
  rw [adjacency_cube hd hd hd, smul_add, smul_add]


/-! ## The first defect, exactly, and the minimum delay it gives

At `d = 4` the Gram defect is a number of `ℚ(√5)`: `cos (π/5) = (1 + √5)/4` gives
`C_N(4)² = (99 − 42 √5) / 5`, so `defectGram 4 = (94 − 42 √5) / 45 ≈ 0.001892`. Times the duration
of a step at the floor `ℓ_P`, `ℓ_P / c`, it is the minimum delay of a step. -/

section DefectFour

open Gnomon Real

theorem sqrt5_sq : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-- `cos² (π/5) = (3 + √5) / 8`. -/
theorem cos_sq_pi_div_five : Real.cos (π / 5) ^ 2 = (3 + √5) / 8 := by
  rw [Real.cos_pi_div_five]
  linear_combination (1 / 16 : ℝ) * sqrt5_sq

/-- `C_N(4)² = (99 − 42 √5) / 5`. -/
theorem coherenceConstantSq_four : CoherenceConstantSq 4 = (99 - 42 * √5) / 5 := by
  unfold CoherenceConstantSq theta Nreal
  have h5 : π / (((4 : ℕ) : ℝ) + 1) = π / 5 := by norm_num
  rw [h5, Real.sin_sq, cos_sq_pi_div_five]
  have hs := sqrt5_sq
  have hpos : (0 : ℝ) < 3 + √5 := by positivity
  field_simp
  ring_nf
  linear_combination 1260 * hs

/-- **The Gram defect of `d = 4`, exactly**: `(94 − 42 √5) / 45`. -/
theorem defectGram_four : defectGram 4 = (94 - 42 * √5) / 45 := by
  rw [gramStep_gram (by norm_num), coherenceConstantSq_four]
  norm_num
  ring

/-- `0.001892 < defectGram 4 < 0.001893`. -/
theorem defectGram_four_bounds : (0.001892 : ℝ) < defectGram 4 ∧ defectGram 4 < 0.001893 := by
  rw [defectGram_four]
  have h1 : (2.2360679 : ℝ) < √5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have h2 : √5 < (2.236068 : ℝ) := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  constructor <;> linarith

/-- **The minimum delay of a step at `d = 4`**, with `ℓ_P = 1.616255 × 10⁻³⁵ m` and
`c = 299792458 m/s`: `defectGram 4 · ℓ_P / c` lies in `(1.02, 1.021) × 10⁻⁴⁶ s`. -/
theorem delay_four_bounds :
    (1.02e-46 : ℝ) < defectGram 4 * (1.616255e-35 / 299792458) ∧
      defectGram 4 * (1.616255e-35 / 299792458) < 1.021e-46 := by
  obtain ⟨h1, h2⟩ := defectGram_four_bounds
  have ht : (0 : ℝ) < 1.616255e-35 / 299792458 := by norm_num
  have a1 := mul_lt_mul_of_pos_right h1 ht
  have a2 := mul_lt_mul_of_pos_right h2 ht
  constructor
  · refine lt_trans ?_ a1
    norm_num
  · refine lt_trans a2 ?_
    norm_num

end DefectFour

end Puente

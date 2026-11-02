import Mathlib

/-!
# The Robertson–Schrödinger defect of the first step is `1 - ‖v‖²`: the Bloch ball

The elementary movement of the algebra is the pair `(T, P)` on two sites: the hop `T = σₓ` and the
position `P = σ_z`. Before it there is only no movement; after it, nothing else is needed. For a
state with Bloch vector `v = (x, y, z)`, `ρ = ½ (1 + x σₓ + y σ_y + z σ_z)`:

* the Bloch vector is the triple of expectations of the three Pauli matrices;
* the variances and the covariance of the pair are `1 - x²`, `1 - z²` and `-x z`;
* the Robertson–Schrödinger defect `Var T · Var P - Cov(T, P)² - ¼ |⟨[T, P]⟩|²` equals
  `1 - (x² + y² + z²)` (`defect_eq`);
* `ρ` is positive exactly when `x² + y² + z² ≤ 1` (`posSemidef_rho_iff`).

So the uncertainty relation of the first step *is* the Bloch ball, and it is saturated exactly on
the sphere, the pure states. The cell of the nucleus is this ball: it carries a state, not a place.
-/

namespace NRS3Hidrogeno

open Matrix Complex
open scoped ComplexOrder

noncomputable section

/-- The Pauli matrix `σₓ`: the hop of the first step. -/
def sx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli matrix `σ_y`. -/
def sy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- The Pauli matrix `σ_z`: the position of the first step. -/
def sz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The state with Bloch vector `(x, y, z)`. -/
def rho (x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + (x : ℂ) • sx + (y : ℂ) • sy + (z : ℂ) • sz)

lemma rho_entries (x y z : ℝ) :
    rho x y z = !![(1 + (z : ℂ)) / 2, ((x : ℂ) - (y : ℂ) * I) / 2;
      ((x : ℂ) + (y : ℂ) * I) / 2, (1 - (z : ℂ)) / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rho, sx, sy, sz] <;> ring

lemma trace_rho_mul (x y z : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (rho x y z * A) =
      (1 + (z : ℂ)) / 2 * A 0 0 + ((x : ℂ) - (y : ℂ) * I) / 2 * A 1 0 +
        (((x : ℂ) + (y : ℂ) * I) / 2 * A 0 1 + (1 - (z : ℂ)) / 2 * A 1 1) := by
  have h00 : rho x y z 0 0 = (1 + (z : ℂ)) / 2 := by rw [rho_entries]; simp
  have h01 : rho x y z 0 1 = ((x : ℂ) - (y : ℂ) * I) / 2 := by rw [rho_entries]; simp
  have h10 : rho x y z 1 0 = ((x : ℂ) + (y : ℂ) * I) / 2 := by rw [rho_entries]; simp
  have h11 : rho x y z 1 1 = (1 - (z : ℂ)) / 2 := by rw [rho_entries]; simp
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h00, h01, h10, h11]

lemma trace_rho (x y z : ℝ) : trace (rho x y z) = 1 := by
  rw [rho_entries, Matrix.trace_fin_two]
  simp
  ring

/-- The expectation of an observable in the state with Bloch vector `(x, y, z)`. -/
def ex (x y z : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (trace (rho x y z * A)).re

lemma sx_mul_sx : sx * sx = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sx, Matrix.mul_apply, Fin.sum_univ_two]

lemma sz_mul_sz : sz * sz = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sz, Matrix.mul_apply, Fin.sum_univ_two]

lemma sx_sz_anti : sx * sz + sz * sx = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sx, sz]

lemma sx_sz_comm : sx * sz - sz * sx = (-2 * I) • sy := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sx, sy, sz, mul_assoc, Complex.I_mul_I] <;> norm_num

/-- **The Bloch vector is the triple of expectations of the Pauli matrices.** -/
lemma ex_sx (x y z : ℝ) : ex x y z sx = x := by
  simp [ex, trace_rho_mul, sx]

lemma ex_sy (x y z : ℝ) : ex x y z sy = y := by
  simp [ex, trace_rho_mul, sy]
  ring

lemma ex_sz (x y z : ℝ) : ex x y z sz = z := by
  simp [ex, trace_rho_mul, sz]
  ring

lemma ex_one (x y z : ℝ) : ex x y z 1 = 1 := by
  unfold ex
  rw [mul_one, trace_rho]
  simp

/-- The variance. -/
def var (x y z : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ex x y z (A * A) - ex x y z A ^ 2

/-- The covariance: symmetrized product minus the product of the means. -/
def cov (x y z : ℝ) (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ex x y z (A * B + B * A) / 2 - ex x y z A * ex x y z B

/-- The expectation of the commutator. -/
def comm (x y z : ℝ) (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := trace (rho x y z * (A * B - B * A))

/-- The Robertson–Schrödinger defect: `Var A · Var B - Cov(A, B)² - ¼ |⟨[A, B]⟩|²`. It is
nonnegative for every state. -/
def defect (x y z : ℝ) (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  var x y z A * var x y z B - cov x y z A B ^ 2 - Complex.normSq (comm x y z A B) / 4

lemma var_sx (x y z : ℝ) : var x y z sx = 1 - x ^ 2 := by
  unfold var
  rw [sx_mul_sx, ex_one, ex_sx]

lemma var_sz (x y z : ℝ) : var x y z sz = 1 - z ^ 2 := by
  unfold var
  rw [sz_mul_sz, ex_one, ex_sz]

lemma cov_sx_sz (x y z : ℝ) : cov x y z sx sz = -(x * z) := by
  unfold cov
  rw [sx_sz_anti, ex_sx, ex_sz]
  simp [ex]

lemma comm_sx_sz (x y z : ℝ) : comm x y z sx sz = (-2 * I) * (y : ℂ) := by
  unfold comm
  rw [sx_sz_comm, Matrix.mul_smul, Matrix.trace_smul]
  have : trace (rho x y z * sy) = (y : ℂ) := by
    simp [trace_rho_mul, sy]
    ring_nf
    simp
  rw [this]
  simp

/-- **The defect of the first step is `1 - ‖v‖²`.** -/
theorem defect_eq (x y z : ℝ) : defect x y z sx sz = 1 - (x ^ 2 + y ^ 2 + z ^ 2) := by
  unfold defect
  rw [var_sx, var_sz, cov_sx_sz, comm_sx_sz]
  have : Complex.normSq ((-2 * I) * (y : ℂ)) = 4 * y ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  rw [this]
  ring

/-- The uncertainty relation of the first step holds exactly in the Bloch ball. -/
theorem defect_nonneg_iff (x y z : ℝ) : 0 ≤ defect x y z sx sz ↔ x ^ 2 + y ^ 2 + z ^ 2 ≤ 1 := by
  rw [defect_eq]
  constructor <;> intro h <;> linarith

/-- **It is saturated exactly on the sphere**: the pure states. -/
theorem defect_eq_zero_iff (x y z : ℝ) : defect x y z sx sz = 0 ↔ x ^ 2 + y ^ 2 + z ^ 2 = 1 := by
  rw [defect_eq]
  constructor <;> intro h <;> linarith

/-! ## The state is positive exactly in the ball -/

lemma det_rho (x y z : ℝ) :
    (rho x y z).det = (((1 - (x ^ 2 + y ^ 2 + z ^ 2)) / 4 : ℝ) : ℂ) := by
  rw [rho_entries, Matrix.det_fin_two_of]
  have hI : I * I = -1 := Complex.I_mul_I
  push_cast
  linear_combination ((y : ℂ) ^ 2 / 4) * hI

lemma rho_isHermitian (x y z : ℝ) : (rho x y z).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho_entries, Matrix.conjTranspose_apply, Complex.conj_ofReal]
  all_goals (apply Complex.ext <;> simp)

/-- **`ρ` is positive exactly when `‖v‖ ≤ 1`: the states of the cell are the Bloch ball.** -/
theorem posSemidef_rho_iff (x y z : ℝ) :
    (rho x y z).PosSemidef ↔ x ^ 2 + y ^ 2 + z ^ 2 ≤ 1 := by
  constructor
  · intro h
    have hd := h.det_nonneg
    rw [det_rho, Complex.zero_le_real] at hd
    linarith
  · intro h
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨rho_isHermitian x y z, fun u => ?_⟩
    set a1 := (u 0).re
    set a2 := (u 0).im
    set b1 := (u 1).re
    set b2 := (u 1).im
    set N := a1 ^ 2 + a2 ^ 2 + (b1 ^ 2 + b2 ^ 2) with hN
    set D := a1 ^ 2 + a2 ^ 2 - (b1 ^ 2 + b2 ^ 2) with hD
    set w1 := a1 * b1 + a2 * b2 with hw1
    set w2 := a1 * b2 - a2 * b1 with hw2
    have hform : star u ⬝ᵥ (rho x y z *ᵥ u) = (((N + z * D + 2 * x * w1 + 2 * y * w2) / 2 : ℝ) : ℂ) := by
      rw [rho_entries]
      apply Complex.ext
      · rw [Complex.ofReal_re]
        simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, hN, hD, hw1, hw2, a1, a2, b1, b2]
        try ring
      · rw [Complex.ofReal_im]
        simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
        try ring
    rw [hform, Complex.zero_le_real]
    have hnorm : D ^ 2 + (2 * w1) ^ 2 + (2 * w2) ^ 2 = N ^ 2 := by
      rw [hN, hD, hw1, hw2]
      ring
    have hcs : (z * D + 2 * x * w1 + 2 * y * w2) ^ 2 ≤
        (x ^ 2 + y ^ 2 + z ^ 2) * (D ^ 2 + (2 * w1) ^ 2 + (2 * w2) ^ 2) := by
      nlinarith [sq_nonneg (z * (2 * w1) - x * D), sq_nonneg (z * (2 * w2) - y * D),
        sq_nonneg (x * (2 * w2) - y * (2 * w1))]
    have hN0 : 0 ≤ N := by rw [hN]; positivity
    have hsq : (z * D + 2 * x * w1 + 2 * y * w2) ^ 2 ≤ N ^ 2 := by
      rw [hnorm] at hcs
      nlinarith [sq_nonneg N]
    have := (abs_le_of_sq_le_sq' hsq hN0).1
    linarith

end

end NRS3Hidrogeno

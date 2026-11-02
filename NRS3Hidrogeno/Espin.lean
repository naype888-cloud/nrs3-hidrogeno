import Mathlib
import NRS3Hidrogeno.Cierre
import NRS3Hidrogeno.BolaDeBloch

/-!
# `(T_d, P_d)` is the spin for `d = 2, 3`

For `d = 2` the hop is `σₓ` and the position is `(1 - σ_z) / 2`: the qubit of `BolaDeBloch`. For
`d = 3`, with `T = Tp 3`, `Y = i [T, P]` and `Z = P - 1`, the three matrices satisfy the relations
of an angular momentum of spin one: `[T, Y] = 2 i Z`, `[Y, Z] = i T`, `[Z, T] = i Y` and the
Casimir `T² + Y² + 2 Z² = 4`, that is `Jₓ = T / √2`, `J_y = Y / √2`, `J_z = Z` with
`J² = j (j + 1) = 2`. (The orientation of `Y` and `Z` is the one of the rotation by `π` around the
first axis of the usual `J_y`, `J_z`.) These are statements about explicit matrices; they say
nothing about `d ≥ 4`, where `Cierre.closes_iff` shows that the commutators do not close.
-/

namespace NRS3Hidrogeno

open Matrix

noncomputable section

/-- The hop of the path of two positions, as a complex matrix: `σₓ`. -/
lemma Tp_two : (Tp 2).map (Complex.ofReal) = sx := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tp, Sh, sx]

/-- The position of two sites, as a complex matrix: `(1 - σ_z) / 2`. -/
lemma Pp_two : (Pp 2).map (Complex.ofReal) = (1 / 2 : ℂ) • (1 - sz) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pp, sz]
  all_goals norm_num

/-- The hop of the path of three positions. -/
def T3 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 1, 0, 1; 0, 1, 0]

/-- `Y = i [T, P]` for three positions. -/
def Y3 : Matrix (Fin 3) (Fin 3) ℂ := !![0, Complex.I, 0; -Complex.I, 0, Complex.I; 0, -Complex.I, 0]

/-- `Z = P - 1` for three positions. -/
def Z3 : Matrix (Fin 3) (Fin 3) ℂ := !![-1, 0, 0; 0, 0, 0; 0, 0, 1]

lemma Tp_three : (Tp 3).map (Complex.ofReal) = T3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tp, Sh, T3]

lemma Pp_three : (Pp 3).map (Complex.ofReal) = Z3 + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pp, Z3]
  all_goals norm_num

lemma Y3_eq : Y3 = Complex.I • ((Tp 3).map (Complex.ofReal) * (Pp 3).map (Complex.ofReal) -
    (Pp 3).map (Complex.ofReal) * (Tp 3).map (Complex.ofReal)) := by
  rw [Tp_three, Pp_three]
  have h : T3 * (Z3 + 1) - (Z3 + 1) * T3 = T3 * Z3 - Z3 * T3 := by
    simp only [mul_add, add_mul, mul_one, one_mul]
    abel
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Y3, T3, Z3]

lemma comm_T3_Y3 : T3 * Y3 - Y3 * T3 = (2 * Complex.I) • Z3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [T3, Y3, Z3]
  all_goals ring

lemma comm_Y3_Z3 : Y3 * Z3 - Z3 * Y3 = Complex.I • T3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [T3, Y3, Z3]

lemma comm_Z3_T3 : Z3 * T3 - T3 * Z3 = Complex.I • Y3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [T3, Y3, Z3]

/-- The Casimir: `T² + Y² + 2 Z² = 4`, that is `J² = 2 = j (j + 1)` with `j = 1`. -/
lemma casimir_three :
    T3 * T3 + Y3 * Y3 + (2 : ℂ) • (Z3 * Z3) = (4 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [T3, Y3, Z3]
  all_goals ring

end

end NRS3Hidrogeno

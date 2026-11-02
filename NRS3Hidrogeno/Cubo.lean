import Mathlib
import Physlib.QuantumMechanics.Hydrogen.Rydberg

/-!
# Hydrogen on the cube: the axis hop plus the Coulomb term

The electron sits on the cells of the cube, the cell `p = (i, j, l)` having its centre at
`((i + 1/2) a, (j + 1/2) a, (l + 1/2) a)`, so the origin is a corner and `r` never vanishes.
The only hop is the axis step `p ↦ p + e_i`; a diagonal is a composition of two of them.
-/

namespace NRS3Hidrogeno

open Finset

/-- The three axis steps of the cube: the only elementary hop. -/
def axis : Fin 3 → ℤ × ℤ × ℤ
  | 0 => (1, 0, 0)
  | 1 => (0, 1, 0)
  | 2 => (0, 0, 1)

/-- Centre of the cell `i` along one axis, for cell side `a`. -/
noncomputable def centre (a : ℝ) (i : ℤ) : ℝ := ((i : ℝ) + 1 / 2) * a

/-- Distance from the origin (a corner of the cube) to the centre of the cell `p`. -/
noncomputable def radius (a : ℝ) (p : ℤ × ℤ × ℤ) : ℝ :=
  √(centre a p.1 ^ 2 + centre a p.2.1 ^ 2 + centre a p.2.2 ^ 2)

lemma centre_sq_ge (a : ℝ) (i : ℤ) : a ^ 2 / 4 ≤ centre a i ^ 2 := by
  have h : (1 : ℝ) / 4 ≤ ((i : ℝ) + 1 / 2) ^ 2 := by
    rcases le_or_gt 0 i with hi | hi
    · have : (0 : ℝ) ≤ i := by exact_mod_cast hi
      nlinarith
    · have : (i : ℝ) ≤ -1 := by exact_mod_cast (by omega : i ≤ -1)
      nlinarith
  unfold centre
  rw [mul_pow]
  nlinarith [sq_nonneg a]

lemma radius_sq_ge (a : ℝ) (p : ℤ × ℤ × ℤ) : 3 * a ^ 2 / 4 ≤ radius a p ^ 2 := by
  unfold radius
  rw [Real.sq_sqrt (by positivity)]
  nlinarith [centre_sq_ge a p.1, centre_sq_ge a p.2.1, centre_sq_ge a p.2.2]

lemma radius_pos {a : ℝ} (ha : 0 < a) (p : ℤ × ℤ × ℤ) : 0 < radius a p := by
  have h := radius_sq_ge a p
  have h0 : 0 ≤ radius a p := Real.sqrt_nonneg _
  by_contra hneg
  have : radius a p = 0 := le_antisymm (not_lt.mp hneg) h0
  rw [this] at h
  nlinarith [sq_pos_of_pos ha]

/-- Kinetic form: sum over the axis hops of the squared differences. -/
noncomputable def kinetic (a : ℝ) (S : Finset (ℤ × ℤ × ℤ)) (ψ : ℤ × ℤ × ℤ → ℝ) : ℝ :=
  (1 / (2 * a ^ 2)) * ∑ p ∈ S, ∑ i : Fin 3, (ψ (p + axis i) - ψ p) ^ 2

/-- Coulomb form `-k / r` on the cells. -/
noncomputable def coulomb (k a : ℝ) (S : Finset (ℤ × ℤ × ℤ)) (ψ : ℤ × ℤ × ℤ → ℝ) : ℝ :=
  -k * ∑ p ∈ S, ψ p ^ 2 / radius a p

/-- Energy form of the hydrogen atom on the cube. -/
noncomputable def energy (k a : ℝ) (S : Finset (ℤ × ℤ × ℤ)) (ψ : ℤ × ℤ × ℤ → ℝ) : ℝ :=
  kinetic a S ψ + coulomb k a S ψ

lemma kinetic_nonneg {a : ℝ} (ha : 0 < a) (S : Finset (ℤ × ℤ × ℤ)) (ψ : ℤ × ℤ × ℤ → ℝ) :
    0 ≤ kinetic a S ψ := by
  unfold kinetic
  have : 0 < 1 / (2 * a ^ 2) := by positivity
  exact mul_nonneg this.le (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- The Coulomb term is bounded below on the cube: the closest cell is at `√3 a / 2`. -/
lemma coulomb_ge {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (S : Finset (ℤ × ℤ × ℤ))
    (ψ : ℤ × ℤ × ℤ → ℝ) :
    -(k * (2 / (√3 * a))) * ∑ p ∈ S, ψ p ^ 2 ≤ coulomb k a S ψ := by
  have hr : ∀ p, √3 * a / 2 ≤ radius a p := by
    intro p
    have h := radius_sq_ge a p
    have h0 := (radius_pos ha p).le
    have h3 : (√3 * a / 2) ^ 2 = 3 * a ^ 2 / 4 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring
    exact abs_le_of_sq_le_sq' (by rw [h3]; exact h) h0 |>.2
  have hs : 0 < √3 * a / 2 := by positivity
  unfold coulomb
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have h1 : ψ p ^ 2 / radius a p ≤ ψ p ^ 2 / (√3 * a / 2) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hs (hr p)
  have h2 : ψ p ^ 2 / (√3 * a / 2) = (2 / (√3 * a)) * ψ p ^ 2 := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left h1 hk]

end NRS3Hidrogeno

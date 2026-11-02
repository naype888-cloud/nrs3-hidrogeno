import Mathlib
import NRS3Hidrogeno.Sitios

/-!
# The speed cap of the cube

The velocity along an axis is `v_i = i [H, x_i]`. On the hop `-t (S_i + S_i†)` it acts as
`(v_i ψ)(p) = i t a (ψ(p - e_i) - ψ(p + e_i))`. Whatever the state and the size of the cube,
`‖v_i ψ‖ ≤ 2 t a ‖ψ‖`: with `t = 1/(2 a²)` (ħ = m = 1) this is `1 / a`. This is an upper bound only.
It is saturated exactly for `d = 2, 3` (`C_N = 1`); from `d = 4` the excess `δ(d) = C_N(d) - 1 > 0`
is the delay of the max current on the diagonal words (corpus `D44`, `D8`), which this file does not prove.
-/

namespace NRS3Hidrogeno

open Finset

/-- The velocity along the axis `i`, `i [H, x_i]`, for hop `t` and cell side `a`. -/
noncomputable def vel (i : Fin 3) (t a : ℝ) (ψ : ℤ × ℤ × ℤ → ℂ) : ℤ × ℤ × ℤ → ℂ :=
  fun p => Complex.I * ((t * a : ℝ) : ℂ) * (ψ (p - axis i) - ψ (p + axis i))

/-- The cells that the hop along the axis `i` can reach from the support `S`. -/
def reach (S : Finset (ℤ × ℤ × ℤ)) (i : Fin 3) : Finset (ℤ × ℤ × ℤ) :=
  S.image (· + axis i) ∪ S.image (· - axis i)

lemma sum_shift_sub (S : Finset (ℤ × ℤ × ℤ)) (ψ : ℤ × ℤ × ℤ → ℂ) (hS : ∀ p ∉ S, ψ p = 0)
    (i : Fin 3) :
    ∑ p ∈ reach S i, ‖ψ (p - axis i)‖ ^ 2 = ∑ q ∈ S, ‖ψ q‖ ^ 2 := by
  have hsub : S.image (· + axis i) ⊆ reach S i := Finset.subset_union_left
  rw [← Finset.sum_subset hsub, Finset.sum_image]
  · simp
  · intro x _ y _ h; simpa using h
  · intro p _ hp
    have : p - axis i ∉ S := by
      intro h
      exact hp (Finset.mem_image.mpr ⟨p - axis i, h, by simp⟩)
    simp [hS _ this]

lemma sum_shift_add (S : Finset (ℤ × ℤ × ℤ)) (ψ : ℤ × ℤ × ℤ → ℂ) (hS : ∀ p ∉ S, ψ p = 0)
    (i : Fin 3) :
    ∑ p ∈ reach S i, ‖ψ (p + axis i)‖ ^ 2 = ∑ q ∈ S, ‖ψ q‖ ^ 2 := by
  have hsub : S.image (· - axis i) ⊆ reach S i := Finset.subset_union_right
  rw [← Finset.sum_subset hsub, Finset.sum_image]
  · simp
  · intro x _ y _ h; simpa using h
  · intro p _ hp
    have : p + axis i ∉ S := by
      intro h
      exact hp (Finset.mem_image.mpr ⟨p + axis i, h, by simp⟩)
    simp [hS _ this]

/-- **The speed cap.** For every state supported in `S`, on any cube, along any axis:
`‖v_i ψ‖² ≤ (2 t a)² ‖ψ‖²`. -/
theorem vel_bound (S : Finset (ℤ × ℤ × ℤ)) (ψ : ℤ × ℤ × ℤ → ℂ) (hS : ∀ p ∉ S, ψ p = 0)
    (i : Fin 3) (t a : ℝ) :
    ∑ p ∈ reach S i, ‖vel i t a ψ p‖ ^ 2 ≤ (2 * t * a) ^ 2 * ∑ q ∈ S, ‖ψ q‖ ^ 2 := by
  have h1 : ∀ p, ‖vel i t a ψ p‖ ^ 2 ≤
      (t * a) ^ 2 * (2 * ‖ψ (p - axis i)‖ ^ 2 + 2 * ‖ψ (p + axis i)‖ ^ 2) := by
    intro p
    have hn : ‖vel i t a ψ p‖ = |t * a| * ‖ψ (p - axis i) - ψ (p + axis i)‖ := by
      simp [vel]
    rw [hn, mul_pow, sq_abs]
    have h2 : ‖ψ (p - axis i) - ψ (p + axis i)‖ ^ 2 ≤
        2 * ‖ψ (p - axis i)‖ ^ 2 + 2 * ‖ψ (p + axis i)‖ ^ 2 := by
      have := norm_sub_le (ψ (p - axis i)) (ψ (p + axis i))
      nlinarith [norm_nonneg (ψ (p - axis i)), norm_nonneg (ψ (p + axis i)),
        norm_nonneg (ψ (p - axis i) - ψ (p + axis i)),
        sq_nonneg (‖ψ (p - axis i)‖ - ‖ψ (p + axis i)‖)]
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  calc ∑ p ∈ reach S i, ‖vel i t a ψ p‖ ^ 2
      ≤ ∑ p ∈ reach S i, (t * a) ^ 2 *
          (2 * ‖ψ (p - axis i)‖ ^ 2 + 2 * ‖ψ (p + axis i)‖ ^ 2) :=
        Finset.sum_le_sum fun p _ => h1 p
    _ = (t * a) ^ 2 * (2 * ∑ q ∈ S, ‖ψ q‖ ^ 2 + 2 * ∑ q ∈ S, ‖ψ q‖ ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          sum_shift_sub S ψ hS i, sum_shift_add S ψ hS i]
    _ = (2 * t * a) ^ 2 * ∑ q ∈ S, ‖ψ q‖ ^ 2 := by ring

/-- With `t = 1 / (2 a²)` (ħ = m = 1) the bound is `1 / a`. It is an upper bound, not the attained speed
for `d ≥ 4`. -/
theorem vel_bound_cube (S : Finset (ℤ × ℤ × ℤ)) (ψ : ℤ × ℤ × ℤ → ℂ) (hS : ∀ p ∉ S, ψ p = 0)
    (i : Fin 3) {a : ℝ} (ha : 0 < a) :
    ∑ p ∈ reach S i, ‖vel i (1 / (2 * a ^ 2)) a ψ p‖ ^ 2 ≤ (1 / a) ^ 2 * ∑ q ∈ S, ‖ψ q‖ ^ 2 := by
  have h := vel_bound S ψ hS i (1 / (2 * a ^ 2)) a
  have e : (2 * (1 / (2 * a ^ 2)) * a) = 1 / a := by field_simp
  rwa [e] at h

end NRS3Hidrogeno

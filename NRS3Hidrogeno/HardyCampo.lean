import Mathlib
import NRS3Hidrogeno.Cinetica

/-!
# Hardy's inequality from a field on the edges

For any real field `κ` on the axis edges of `ℤ³`, every state `ψ` supported in a finite set `S`
satisfies `Σ_S w(p) ψ(p)² ≤ Σ over the axis edges of the squared differences`, where `w` is the
coefficient `wVF κ` that the field produces on each site. The inequality is the sum, over the edges,
of `2 κ (a² - b²) - 2 κ² (a² + b²) ≤ (b - a)²` (`edge_vf`). It carries no cell side and no size of
the box. The field used on the integer sites is in `HardyEntero`.
-/

namespace NRS3Hidrogeno

open Finset

/-- The edge inequality with a free multiplier `κ`. -/
lemma edge_vf (a b κ : ℝ) : 2 * κ * (a ^ 2 - b ^ 2) - 2 * κ ^ 2 * (a ^ 2 + b ^ 2) ≤ (b - a) ^ 2 := by
  nlinarith [sq_nonneg (b - a + κ * (a + b)), mul_nonneg (sq_nonneg κ) (sq_nonneg (a - b))]

/-- The coefficient of `ψ(p)²` that a field `κ` produces, summed over the three axes. -/
noncomputable def wVF (κ : Fin 3 → ℤ × ℤ × ℤ → ℝ) (p : ℤ × ℤ × ℤ) : ℝ :=
  ∑ i : Fin 3, (2 * κ i p - 2 * κ i (p - axis i) - 2 * (κ i p) ^ 2 - 2 * (κ i (p - axis i)) ^ 2)

/-- **Hardy from a field on the edges.** -/
theorem hardy_vf (S : Finset (ℤ × ℤ × ℤ)) (κ : Fin 3 → ℤ × ℤ × ℤ → ℝ) (ψ : ℤ × ℤ × ℤ → ℝ)
    (hψ : ∀ p ∉ S, ψ p = 0) :
    ∑ p ∈ S, wVF κ p * ψ p ^ 2 ≤
      ∑ i : Fin 3, ∑ p ∈ edgeBase S i, (ψ (p + axis i) - ψ p) ^ 2 := by
  have per : ∀ i : Fin 3,
      ∑ p ∈ S, (2 * κ i p - 2 * κ i (p - axis i) - 2 * (κ i p) ^ 2 - 2 * (κ i (p - axis i)) ^ 2) *
        ψ p ^ 2 ≤ ∑ p ∈ edgeBase S i, (ψ (p + axis i) - ψ p) ^ 2 := by
    intro i
    have e1 : ∑ p ∈ edgeBase S i, (2 * κ i p - 2 * (κ i p) ^ 2) * ψ p ^ 2 =
        ∑ p ∈ S, (2 * κ i p - 2 * (κ i p) ^ 2) * ψ p ^ 2 :=
      sum_edgeBase_self S (fun p => (2 * κ i p - 2 * (κ i p) ^ 2) * ψ p ^ 2)
        (fun p hp => by simp [hψ p hp]) i
    have e2 : ∑ p ∈ edgeBase S i, (-2 * κ i p - 2 * (κ i p) ^ 2) * ψ (p + axis i) ^ 2 =
        ∑ p ∈ S, (-2 * κ i (p - axis i) - 2 * (κ i (p - axis i)) ^ 2) * ψ p ^ 2 := by
      have := sum_edgeBase_shift S
        (fun q => (-2 * κ i (q - axis i) - 2 * (κ i (q - axis i)) ^ 2) * ψ q ^ 2)
        (fun p hp => by simp [hψ p hp]) i
      simpa only [add_sub_cancel_right] using this
    calc ∑ p ∈ S, (2 * κ i p - 2 * κ i (p - axis i) - 2 * (κ i p) ^ 2 -
            2 * (κ i (p - axis i)) ^ 2) * ψ p ^ 2
        = ∑ p ∈ S, (2 * κ i p - 2 * (κ i p) ^ 2) * ψ p ^ 2 +
          ∑ p ∈ S, (-2 * κ i (p - axis i) - 2 * (κ i (p - axis i)) ^ 2) * ψ p ^ 2 := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun p _ => by ring
      _ = ∑ p ∈ edgeBase S i, ((2 * κ i p - 2 * (κ i p) ^ 2) * ψ p ^ 2 +
          (-2 * κ i p - 2 * (κ i p) ^ 2) * ψ (p + axis i) ^ 2) := by
          rw [Finset.sum_add_distrib, e1, e2]
      _ ≤ _ := Finset.sum_le_sum fun p _ => by
          nlinarith [edge_vf (ψ p) (ψ (p + axis i)) (κ i p)]
  calc ∑ p ∈ S, wVF κ p * ψ p ^ 2
      = ∑ i : Fin 3, ∑ p ∈ S, (2 * κ i p - 2 * κ i (p - axis i) - 2 * (κ i p) ^ 2 -
          2 * (κ i (p - axis i)) ^ 2) * ψ p ^ 2 := by
        unfold wVF
        simp_rw [Finset.sum_mul]
        exact Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun i _ => per i

end NRS3Hidrogeno

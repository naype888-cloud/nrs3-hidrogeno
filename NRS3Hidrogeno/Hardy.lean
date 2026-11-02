import Mathlib
import NRS3Hidrogeno.Limite

/-!
# A discrete Hardy inequality from a positive supersolution

If `w > 0` on the cells and `(L w)(p) = Σᵢ (2 w(p) - w(p + eᵢ) - w(p - eᵢ)) ≥ λ V(p) w(p)`, then for every state
supported in a finite set `S`, the sum over the axis edges of the squared differences is at least
`λ Σ V ψ²` (ground state representation, `ψ = w φ`). With `V = 1 / r²` this is Hardy's inequality
on the cube, and it gives a lower bound of the ground energy that does not depend on the cell `a`
nor on the size of the cube.

The existence of the supersolution `w = r^(-α)` with `λ > 0` is a hypothesis here
(`SuperSolution`): numerically `λ ≈ 0.16` for `α = 0.4`; it is not proved.
-/

namespace NRS3Hidrogeno

open Finset

/-- `L w`: twice `w` minus its two neighbours, summed over the three axes. -/
def lap (w : ℤ × ℤ × ℤ → ℝ) (p : ℤ × ℤ × ℤ) : ℝ :=
  ∑ i : Fin 3, (2 * w p - w (p + axis i) - w (p - axis i))

lemma edge_ineq {wp wq a b : ℝ} (hp : 0 < wp) (hq : 0 < wq) :
    (wp - wq) * (a ^ 2 / wp - b ^ 2 / wq) ≤ (b - a) ^ 2 := by
  have key : (b - a) ^ 2 - (wp - wq) * (a ^ 2 / wp - b ^ 2 / wq) =
      wp * wq * (a / wp - b / wq) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ wp * wq * (a / wp - b / wq) ^ 2 := by positivity
  linarith

lemma sum_axis (S : Finset (ℤ × ℤ × ℤ)) (w ψ : ℤ × ℤ × ℤ → ℝ) (hψ : ∀ p ∉ S, ψ p = 0)
    (i : Fin 3) :
    ∑ p ∈ edgeBase S i, (w p - w (p + axis i)) * (ψ p ^ 2 / w p - ψ (p + axis i) ^ 2 / w (p + axis i))
      = ∑ p ∈ S, ψ p ^ 2 / w p * (2 * w p - w (p + axis i) - w (p - axis i)) := by
  have hz : ∀ p ∉ S, ψ p ^ 2 / w p = 0 := fun p hp => by simp [hψ p hp]
  have e1 := sum_edgeBase_self S (fun p => (w p - w (p + axis i)) * (ψ p ^ 2 / w p))
    (fun p hp => by simp [hz p hp]) i
  have e2 := sum_edgeBase_shift S
    (fun q => (w (q - axis i) - w q) * (ψ q ^ 2 / w q)) (fun p hp => by simp [hz p hp]) i
  simp only [add_sub_cancel_right] at e2
  have : ∀ p, (w p - w (p + axis i)) * (ψ p ^ 2 / w p - ψ (p + axis i) ^ 2 / w (p + axis i)) =
      (w p - w (p + axis i)) * (ψ p ^ 2 / w p) -
        (w p - w (p + axis i)) * (ψ (p + axis i) ^ 2 / w (p + axis i)) := fun p => by ring
  simp_rw [this]
  rw [Finset.sum_sub_distrib, e1, e2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- **Hardy from a supersolution.** -/
theorem hardy_of_supersolution (S : Finset (ℤ × ℤ × ℤ)) (w V ψ : ℤ × ℤ × ℤ → ℝ) {lam : ℝ}
    (hw : ∀ p, 0 < w p) (hψ : ∀ p ∉ S, ψ p = 0)
    (hs : ∀ p, lam * V p * w p ≤ lap w p) :
    lam * ∑ p ∈ S, V p * ψ p ^ 2 ≤
      ∑ i : Fin 3, ∑ p ∈ edgeBase S i, (ψ (p + axis i) - ψ p) ^ 2 := by
  calc lam * ∑ p ∈ S, V p * ψ p ^ 2
      = ∑ p ∈ S, ψ p ^ 2 / w p * (lam * V p * w p) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        have := (hw p).ne'
        field_simp
    _ ≤ ∑ p ∈ S, ψ p ^ 2 / w p * lap w p :=
        Finset.sum_le_sum fun p _ =>
          mul_le_mul_of_nonneg_left (hs p) (div_nonneg (sq_nonneg _) (hw p).le)
    _ = ∑ i : Fin 3, ∑ p ∈ S, ψ p ^ 2 / w p * (2 * w p - w (p + axis i) - w (p - axis i)) := by
        unfold lap
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ i : Fin 3, ∑ p ∈ edgeBase S i, (w p - w (p + axis i)) *
          (ψ p ^ 2 / w p - ψ (p + axis i) ^ 2 / w (p + axis i)) :=
        (Finset.sum_congr rfl fun i _ => (sum_axis S w ψ hψ i).symm)
    _ ≤ ∑ i : Fin 3, ∑ p ∈ edgeBase S i, (ψ (p + axis i) - ψ p) ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun p _ => edge_ineq (hw p) (hw _)

lemma radius_scale {a : ℝ} (ha : 0 < a) (p : ℤ × ℤ × ℤ) : radius a p = a * radius 1 p := by
  unfold radius centre
  have h : (((p.1 : ℝ) + 1 / 2) * a) ^ 2 + (((p.2.1 : ℝ) + 1 / 2) * a) ^ 2 +
      (((p.2.2 : ℝ) + 1 / 2) * a) ^ 2 = a ^ 2 * ((((p.1 : ℝ) + 1 / 2) * 1) ^ 2 +
      (((p.2.1 : ℝ) + 1 / 2) * 1) ^ 2 + (((p.2.2 : ℝ) + 1 / 2) * 1) ^ 2) := by ring
  rw [h, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]

/-- **The ground energy of the cube is bounded below, uniformly in the cell and the size of the
cube**, given a positive supersolution of `1 / r²` (`lap w ≥ λ w / r²`). -/
theorem energyFull_ge_uniform {k a lam : ℝ} (ha : 0 < a) (hl : 0 < lam)
    {w : ℤ × ℤ × ℤ → ℝ} (hw : ∀ p, 0 < w p)
    (hsup : ∀ p, lam * (1 / radius 1 p ^ 2) * w p ≤ lap w p) {M : ℕ} {ψ : ℤ × ℤ × ℤ → ℝ}
    (hψ : ψ ∈ Unit M) : -(k ^ 2 / (2 * lam)) ≤ energyFull k a (cubo M) ψ := by
  have hr : ∀ p, 0 < radius 1 p := fun p => radius_pos one_pos p
  have hH := hardy_of_supersolution (cubo M) w (fun p => 1 / radius 1 p ^ 2) ψ hw hψ.1 hsup
  set T := ∑ i : Fin 3, ∑ p ∈ edgeBase (cubo M) i, (ψ (p + axis i) - ψ p) ^ 2 with hT
  set X := ∑ p ∈ cubo M, ψ p ^ 2 / radius 1 p with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun p _ => div_nonneg (sq_nonneg _) (hr p).le
  have hcs : X ^ 2 ≤ ∑ p ∈ cubo M, 1 / radius 1 p ^ 2 * ψ p ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (cubo M) (fun p => ψ p / radius 1 p) ψ
    have e1 : ∑ p ∈ cubo M, ψ p / radius 1 p * ψ p = X := by
      rw [hX]
      exact Finset.sum_congr rfl fun p _ => by have := (hr p).ne'; field_simp
    have e2 : ∑ p ∈ cubo M, (ψ p / radius 1 p) ^ 2 = ∑ p ∈ cubo M, 1 / radius 1 p ^ 2 * ψ p ^ 2 :=
      Finset.sum_congr rfl fun p _ => by have := (hr p).ne'; field_simp
    rw [e1, e2, hψ.2, mul_one] at h
    exact h
  have hlX : lam * X ^ 2 ≤ T := le_trans (mul_le_mul_of_nonneg_left hcs hl.le) hH
  have hk1 : kineticFull a (cubo M) ψ = 1 / (2 * a ^ 2) * T := rfl
  have hc1 : coulomb k a (cubo M) ψ = -(k * (X / a)) := by
    unfold coulomb
    have hs : ∑ p ∈ cubo M, ψ p ^ 2 / radius a p = X / a := by
      rw [hX, Finset.sum_div]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [radius_scale ha p]
      have := (hr p).ne'
      have := ha.ne'
      field_simp
    rw [hs]
    ring
  unfold energyFull
  rw [hk1, hc1]
  have h2 : lam * X ^ 2 / (2 * a ^ 2) - k * X / a + k ^ 2 / (2 * lam) =
      (lam * X - k * a) ^ 2 / (2 * a ^ 2 * lam) := by
    have := ha.ne'; have := hl.ne'
    field_simp
    ring
  have h3 : 0 ≤ (lam * X - k * a) ^ 2 / (2 * a ^ 2 * lam) := by positivity
  have h4 : lam * X ^ 2 / (2 * a ^ 2) ≤ 1 / (2 * a ^ 2) * T := by
    rw [one_div, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right hlX (by positivity)
  have h5 : k * (X / a) = k * X / a := by ring
  rw [h5]
  linarith

/-- **The ground energy of every cube is at least `-k² / (2 λ)`**: no dependence on `a` nor `M`. -/
theorem le_groundEnergy_uniform {k a lam : ℝ} (ha : 0 < a) (hl : 0 < lam)
    {w : ℤ × ℤ × ℤ → ℝ} (hw : ∀ p, 0 < w p)
    (hsup : ∀ p, lam * (1 / radius 1 p ^ 2) * w p ≤ lap w p) {M : ℕ} (hM : 1 ≤ M) :
    -(k ^ 2 / (2 * lam)) ≤ groundEnergy k a M := by
  have : Nonempty (Unit M) := ⟨⟨trial, trial_unit hM⟩⟩
  exact le_ciInf fun ψ => energyFull_ge_uniform ha hl hw hsup ψ.2

end NRS3Hidrogeno

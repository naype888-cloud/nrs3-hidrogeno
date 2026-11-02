import Mathlib
import NRS3Hidrogeno.Variacional

/-!
# The block of `8` cells as a trial state

The `8` cells around the origin corner, each with amplitude `s = 1/√8`: the kinetic form is
`3 / (2 a²)` (the `12` internal edges cost nothing, the `24` outer ones cost `1/8` each), and
every cell is at `√3 a / 2` of the origin, so the Coulomb form is `-2 k / (√3 a)`.
-/

namespace NRS3Hidrogeno

open Finset

/-- Amplitude of the trial state. -/
noncomputable def s : ℝ := (√8)⁻¹

lemma s_sq : s ^ 2 = 1 / 8 := by
  unfold s; rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- The trial state: the block `cubo 1` of `8` cells. -/
noncomputable def trial : ℤ × ℤ × ℤ → ℝ := fun p => if p ∈ cubo 1 then s else 0

lemma card_cubo_one : (cubo 1).card = 8 := by
  have := card_cubo 1; simpa using this

lemma cubo_mono {M : ℕ} (hM : 1 ≤ M) : cubo 1 ⊆ cubo M := by
  intro p hp
  simp only [cubo, Finset.mem_product, Finset.mem_Ico] at hp ⊢
  have : (1 : ℤ) ≤ M := by exact_mod_cast hM
  omega

lemma trial_zero {M : ℕ} (hM : 1 ≤ M) : ∀ p ∉ cubo M, trial p = 0 := by
  intro p hp
  have : p ∉ cubo 1 := fun h => hp (cubo_mono hM h)
  simp [trial, this]

lemma sum_trial_sq {M : ℕ} (hM : 1 ≤ M) : ∑ p ∈ cubo M, trial p ^ 2 = 1 := by
  rw [← Finset.sum_subset (cubo_mono hM) (fun p _ hp => by
    have : p ∉ cubo 1 := hp
    simp [trial, this])]
  rw [Finset.sum_congr rfl (fun p hp => by simp [trial, hp] : ∀ p ∈ cubo 1, trial p ^ 2 = s ^ 2)]
  rw [Finset.sum_const, card_cubo_one, s_sq]; norm_num

lemma trial_unit {M : ℕ} (hM : 1 ≤ M) : trial ∈ Unit M := ⟨trial_zero hM, sum_trial_sq hM⟩

lemma centre_sq_of_mem {a : ℝ} {i : ℤ} (hi : i ∈ Finset.Ico (-(1 : ℤ)) 1) :
    centre a i ^ 2 = a ^ 2 / 4 := by
  rw [Finset.mem_Ico] at hi
  have : i = -1 ∨ i = 0 := by omega
  rcases this with rfl | rfl <;> simp [centre] <;> ring

lemma radius_of_mem {a : ℝ} (ha : 0 < a) {p : ℤ × ℤ × ℤ} (hp : p ∈ cubo 1) :
    radius a p = √3 * a / 2 := by
  simp only [cubo, Finset.mem_product] at hp
  unfold radius
  rw [centre_sq_of_mem hp.1, centre_sq_of_mem hp.2.1, centre_sq_of_mem hp.2.2]
  rw [show a ^ 2 / 4 + a ^ 2 / 4 + a ^ 2 / 4 = (√3 * a / 2) ^ 2 by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring]
  exact Real.sqrt_sq (by positivity)

lemma coulomb_trial {k a : ℝ} (ha : 0 < a) {M : ℕ} (hM : 1 ≤ M) :
    coulomb k a (cubo M) trial = -(k * (2 / (√3 * a))) := by
  unfold coulomb
  have key : ∀ p ∈ cubo 1, trial p ^ 2 / radius a p = s ^ 2 / (√3 * a / 2) := by
    intro p hp
    rw [radius_of_mem ha hp]
    simp [trial, hp]
  rw [← Finset.sum_subset (cubo_mono hM) (fun p _ hp => by
    have : p ∉ cubo 1 := hp
    simp [trial, this]), Finset.sum_congr rfl key, Finset.sum_const, card_cubo_one, s_sq]
  have h3 : (√3 : ℝ) ≠ 0 := by positivity
  have ha' : a ≠ 0 := ha.ne'
  simp only [nsmul_eq_mul]
  push_cast
  field_simp

lemma adj_trial {M : ℕ} (hM : 1 ≤ M) : adjForm (cubo M) trial = 3 := by
  have hax : ∀ i : Fin 3,
      ∑ p ∈ edgeBase (cubo M) i, 2 * (trial p * trial (p + axis i)) = 1 := by
    intro i
    have hsub : cubo 1 ⊆ edgeBase (cubo M) i := fun p hp =>
      Finset.mem_union_left _ (cubo_mono hM hp)
    have hc : ((cubo 1).filter (fun p => p + axis i ∈ cubo 1)).card = 4 := by
      fin_cases i <;> decide +kernel
    have key : ∀ p ∈ cubo 1, 2 * (trial p * trial (p + axis i)) =
        if p + axis i ∈ cubo 1 then 2 * s ^ 2 else 0 := by
      intro p hp
      by_cases h : p + axis i ∈ cubo 1
      · simp [trial, hp, h]; ring
      · simp [trial, hp, h]
    rw [← Finset.sum_subset hsub (fun p _ hp => by
      have : p ∉ cubo 1 := hp
      simp [trial, this]), Finset.sum_congr rfl key, ← Finset.sum_filter, Finset.sum_const, hc,
      s_sq]
    norm_num
  unfold adjForm
  rw [Fin.sum_univ_three, hax 0, hax 1, hax 2]; norm_num

/-- The energy of the trial block: `3 / (2 a²) - 2 k / (√3 a)`. -/
theorem energy_trial {k a : ℝ} (ha : 0 < a) {M : ℕ} (hM : 1 ≤ M) :
    energyFull k a (cubo M) trial = 3 / (2 * a ^ 2) - k * (2 / (√3 * a)) := by
  unfold energyFull
  rw [kineticFull_eq a (cubo M) trial (trial_zero hM), sum_trial_sq hM, adj_trial hM,
    coulomb_trial ha hM]
  field_simp
  ring

/-- **An upper bound for the ground energy of the cube.** -/
theorem groundEnergy_le_block {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) {M : ℕ} (hM : 1 ≤ M) :
    groundEnergy k a M ≤ 3 / (2 * a ^ 2) - k * (2 / (√3 * a)) := by
  rw [← energy_trial (k := k) ha hM]
  exact groundEnergy_le hk ha M (trial_unit hM)

end NRS3Hidrogeno

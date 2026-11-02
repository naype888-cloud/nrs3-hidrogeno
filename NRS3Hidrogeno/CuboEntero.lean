import Mathlib
import NRS3Hidrogeno.HardyEntero
import NRS3Hidrogeno.Cinetica

/-!
# Hydrogen on the integer sites of the cube

The electron sits on the sites `p ∈ ℤ³ \ {0}` of the box of half-side `M`; the cell `0` is the
nucleus and carries no position. The distance to the nucleus is `a √(p₁² + p₂² + p₃²) ≥ a`: there
is no distance below one step. The only hop is the axis step `p ↦ p + e_i`.

* the energy is bounded below by `-k / a` (the closest site is at `a`) and, by Hardy's inequality
  on the integer sites (`hardy_entero`), by `-2 k²` for every `a` and every box;
* a single site next to the nucleus is a unit state of energy `3 / a² - k / a`.
-/

namespace NRS3Hidrogeno

open Finset

noncomputable section

/-- The sites of the box of half-side `M`, without the nucleus cell. -/
def cuboE (M : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc (-(M : ℤ)) M) ×ˢ (Finset.Icc (-(M : ℤ)) M) ×ˢ (Finset.Icc (-(M : ℤ)) M)).erase 0

lemma zero_notMem_cuboE (M : ℕ) : (0 : ℤ × ℤ × ℤ) ∉ cuboE M := by
  simp [cuboE]

lemma ne_zero_of_mem_cuboE {M : ℕ} {p : ℤ × ℤ × ℤ} (hp : p ∈ cuboE M) : p ≠ 0 := by
  rintro rfl
  exact zero_notMem_cuboE M hp

/-- The distance from the nucleus cell, for cell side `a`. -/
def radiusE (a : ℝ) (p : ℤ × ℤ × ℤ) : ℝ := a * √(RN p)

lemma RN_nonneg (p : ℤ × ℤ × ℤ) : 0 ≤ RN p := by
  unfold RN
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

lemma sqrt_RN_ge_one {p : ℤ × ℤ × ℤ} (hp : p ≠ 0) : 1 ≤ √(RN p) := by
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_le_sqrt (RN_ge_one p hp)

lemma radiusE_ge {a : ℝ} (ha : 0 < a) {p : ℤ × ℤ × ℤ} (hp : p ≠ 0) : a ≤ radiusE a p := by
  unfold radiusE
  nlinarith [sqrt_RN_ge_one hp]

lemma radiusE_pos {a : ℝ} (ha : 0 < a) {p : ℤ × ℤ × ℤ} (hp : p ≠ 0) : 0 < radiusE a p :=
  lt_of_lt_of_le ha (radiusE_ge ha hp)

/-- Coulomb form `-k / r` on the sites. -/
def coulombE (k a : ℝ) (S : Finset (ℤ × ℤ × ℤ)) (ψ : ℤ × ℤ × ℤ → ℝ) : ℝ :=
  -k * ∑ p ∈ S, ψ p ^ 2 / radiusE a p

/-- The energy form: every axis edge that touches the support, plus the Coulomb form. -/
def energyE (k a : ℝ) (S : Finset (ℤ × ℤ × ℤ)) (ψ : ℤ × ℤ × ℤ → ℝ) : ℝ :=
  kineticFull a S ψ + coulombE k a S ψ

/-- Unit states of the box: zero outside the sites, in particular zero on the nucleus cell. -/
def UnitE (M : ℕ) : Set (ℤ × ℤ × ℤ → ℝ) :=
  {ψ | (∀ p ∉ cuboE M, ψ p = 0) ∧ ∑ p ∈ cuboE M, ψ p ^ 2 = 1}

/-- The ground energy of the box of half-side `M`. -/
def groundE (k a : ℝ) (M : ℕ) : ℝ := ⨅ ψ : UnitE M, energyE k a (cuboE M) ψ

/-! ## Lower bounds -/

/-- The closest site is at `a`: the Coulomb form is bounded below by `-k / a`. -/
lemma coulombE_ge {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) {M : ℕ} (ψ : ℤ × ℤ × ℤ → ℝ) :
    -(k / a) * ∑ p ∈ cuboE M, ψ p ^ 2 ≤ coulombE k a (cuboE M) ψ := by
  unfold coulombE
  have h : ∑ p ∈ cuboE M, ψ p ^ 2 / radiusE a p ≤ ∑ p ∈ cuboE M, ψ p ^ 2 / a :=
    Finset.sum_le_sum fun p hp =>
      div_le_div_of_nonneg_left (sq_nonneg _) ha (radiusE_ge ha (ne_zero_of_mem_cuboE hp))
  rw [← Finset.sum_div] at h
  have := mul_le_mul_of_nonneg_left h hk
  have e : -(k / a) * ∑ p ∈ cuboE M, ψ p ^ 2 = -(k * ((∑ p ∈ cuboE M, ψ p ^ 2) / a)) := by
    ring
  rw [e]
  linarith

lemma kineticE_nonneg {a : ℝ} (S : Finset (ℤ × ℤ × ℤ)) (ψ : ℤ × ℤ × ℤ → ℝ) :
    0 ≤ kineticFull a S ψ := by
  unfold kineticFull
  have : 0 ≤ 1 / (2 * a ^ 2) := by positivity
  exact mul_nonneg this (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun p _ => sq_nonneg _)

lemma energyE_ge {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) {M : ℕ} {ψ : ℤ × ℤ × ℤ → ℝ}
    (hψ : ψ ∈ UnitE M) : -(k / a) ≤ energyE k a (cuboE M) ψ := by
  have h := coulombE_ge hk ha (M := M) ψ
  rw [hψ.2, mul_one] at h
  unfold energyE
  linarith [kineticE_nonneg (a := a) (cuboE M) ψ]

lemma bddBelowE {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (M : ℕ) :
    BddBelow (Set.range fun ψ : UnitE M => energyE k a (cuboE M) ψ) :=
  ⟨-(k / a), by rintro _ ⟨ψ, rfl⟩; exact energyE_ge hk ha ψ.2⟩

/-- **Variational principle**: every unit state bounds the ground energy above. -/
theorem groundE_le {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (M : ℕ) {ψ : ℤ × ℤ × ℤ → ℝ}
    (hψ : ψ ∈ UnitE M) : groundE k a M ≤ energyE k a (cuboE M) ψ :=
  ciInf_le (bddBelowE hk ha M) ⟨ψ, hψ⟩

theorem le_groundE {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (M : ℕ) [Nonempty (UnitE M)] :
    -(k / a) ≤ groundE k a M :=
  le_ciInf fun ψ => energyE_ge hk ha ψ.2

/-- **Hardy's inequality bounds the energy below by `-2 k²`**, for every cell `a` and every box:
no dependence on `a` nor `M`. -/
theorem energyE_ge_hardy {k a : ℝ} (ha : 0 < a) {M : ℕ} {ψ : ℤ × ℤ × ℤ → ℝ}
    (hψ : ψ ∈ UnitE M) : -(k ^ 2 / (2 * (1 / 4))) ≤ energyE k a (cuboE M) ψ := by
  have hr : ∀ p ∈ cuboE M, 0 < √(RN p) := fun p hp =>
    lt_of_lt_of_le one_pos (sqrt_RN_ge_one (ne_zero_of_mem_cuboE hp))
  set T := ∑ i : Fin 3, ∑ p ∈ edgeBase (cuboE M) i, (ψ (p + axis i) - ψ p) ^ 2 with hT
  set X := ∑ p ∈ cuboE M, ψ p ^ 2 / √(RN p) with hX
  have hH := hardy_entero (cuboE M) ψ hψ.1 (hψ.1 0 (zero_notMem_cuboE M))
  have hcs : X ^ 2 ≤ ∑ p ∈ cuboE M, (1 / RN p) * ψ p ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (cuboE M) (fun p => ψ p / √(RN p)) ψ
    have e1 : ∑ p ∈ cuboE M, ψ p / √(RN p) * ψ p = X := by
      rw [hX]
      exact Finset.sum_congr rfl fun p hp => by have := (hr p hp).ne'; field_simp
    have e2 : ∑ p ∈ cuboE M, (ψ p / √(RN p)) ^ 2 = ∑ p ∈ cuboE M, (1 / RN p) * ψ p ^ 2 := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [div_pow, Real.sq_sqrt (RN_nonneg p)]
      ring
    rw [e1, e2, hψ.2, mul_one] at h
    exact h
  have hlX : (1 / 4) * X ^ 2 ≤ T := le_trans (mul_le_mul_of_nonneg_left hcs (by norm_num)) hH
  have hk1 : kineticFull a (cuboE M) ψ = 1 / (2 * a ^ 2) * T := rfl
  have hc1 : coulombE k a (cuboE M) ψ = -(k * (X / a)) := by
    unfold coulombE
    have hs : ∑ p ∈ cuboE M, ψ p ^ 2 / radiusE a p = X / a := by
      rw [hX, Finset.sum_div]
      refine Finset.sum_congr rfl fun p hp => ?_
      unfold radiusE
      have := (hr p hp).ne'
      have := ha.ne'
      field_simp
    rw [hs]
    ring
  unfold energyE
  rw [hk1, hc1]
  have h2 : (1 / 4) * X ^ 2 / (2 * a ^ 2) - k * X / a + k ^ 2 / (2 * (1 / 4)) =
      ((1 / 4) * X - k * a) ^ 2 / (2 * a ^ 2 * (1 / 4)) := by
    have := ha.ne'
    field_simp
    ring
  have h3 : 0 ≤ ((1 / 4) * X - k * a) ^ 2 / (2 * a ^ 2 * (1 / 4)) := by positivity
  have h4 : (1 / 4) * X ^ 2 / (2 * a ^ 2) ≤ 1 / (2 * a ^ 2) * T := by
    have e : (1 / 4) * X ^ 2 / (2 * a ^ 2) = 1 / (2 * a ^ 2) * ((1 / 4) * X ^ 2) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hlX (by positivity)
  have h5 : k * (X / a) = k * X / a := by ring
  rw [h5]
  linarith

/-! ## A trial state: one site next to the nucleus -/

/-- The site `(1, 0, 0)`, next to the nucleus cell. -/
def e1 : ℤ × ℤ × ℤ := (1, 0, 0)

/-- The trial state: the unit state on that site. -/
def trialE : ℤ × ℤ × ℤ → ℝ := fun p => if p = e1 then 1 else 0

lemma e1_mem {M : ℕ} (hM : 1 ≤ M) : e1 ∈ cuboE M := by
  have : (1 : ℤ) ≤ M := by exact_mod_cast hM
  simp [cuboE, e1]
  all_goals omega

lemma trialE_zero {M : ℕ} (hM : 1 ≤ M) : ∀ p ∉ cuboE M, trialE p = 0 := by
  intro p hp
  have : p ≠ e1 := fun h => hp (h ▸ e1_mem hM)
  simp [trialE, this]

lemma sum_trialE {M : ℕ} (hM : 1 ≤ M) : ∑ p ∈ cuboE M, trialE p ^ 2 = 1 := by
  rw [Finset.sum_eq_single e1]
  · simp [trialE]
  · intro p _ hp
    simp [trialE, hp]
  · intro h
    exact absurd (e1_mem hM) h

lemma trialE_unit {M : ℕ} (hM : 1 ≤ M) : trialE ∈ UnitE M :=
  ⟨trialE_zero hM, sum_trialE hM⟩

lemma RN_e1 : RN e1 = 1 := by
  rw [RN_eq]
  simp [xi, e1]

lemma radiusE_e1 (a : ℝ) : radiusE a e1 = a := by
  unfold radiusE
  rw [RN_e1]
  simp

lemma coulombE_trial {k a : ℝ} {M : ℕ} (hM : 1 ≤ M) :
    coulombE k a (cuboE M) trialE = -(k / a) := by
  unfold coulombE
  rw [Finset.sum_eq_single e1]
  · simp [trialE, radiusE_e1, div_eq_mul_inv]
  · intro p _ hp
    simp [trialE, hp]
  · intro h
    exact absurd (e1_mem hM) h

lemma axis_ne_zero (i : Fin 3) : axis i ≠ 0 := by
  fin_cases i <;> simp [axis]

lemma adjE_trial (M : ℕ) : adjForm (cuboE M) trialE = 0 := by
  unfold adjForm
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun p _ => ?_
  by_cases hp : p = e1
  · have : p + axis i ≠ e1 := by
      rw [hp]
      intro h
      exact axis_ne_zero i (by simpa using h)
    simp [trialE, this]
  · simp [trialE, hp]

/-- The energy of the trial site: `3 / a² - k / a`. -/
theorem energyE_trial {k a : ℝ} (ha : 0 < a) {M : ℕ} (hM : 1 ≤ M) :
    energyE k a (cuboE M) trialE = 3 / a ^ 2 - k / a := by
  unfold energyE
  rw [kineticFull_eq a (cuboE M) trialE (trialE_zero hM), sum_trialE hM, adjE_trial,
    coulombE_trial hM]
  have := ha.ne'
  field_simp
  ring

/-- **An upper bound for the ground energy of the box.** -/
theorem groundE_le_trial {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) {M : ℕ} (hM : 1 ≤ M) :
    groundE k a M ≤ 3 / a ^ 2 - k / a := by
  rw [← energyE_trial (k := k) ha hM]
  exact groundE_le hk ha M (trialE_unit hM)

/-- **The ground energy of every box is at least `-2 k²`**, for every cell `a`. -/
theorem le_groundE_hardy {k a : ℝ} (ha : 0 < a) {M : ℕ} (hM : 1 ≤ M) :
    -(k ^ 2 / (2 * (1 / 4))) ≤ groundE k a M := by
  have : Nonempty (UnitE M) := ⟨⟨trialE, trialE_unit hM⟩⟩
  exact le_ciInf fun ψ => energyE_ge_hardy ha ψ.2

end

end NRS3Hidrogeno

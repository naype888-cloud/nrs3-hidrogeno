import Mathlib

/-!
# The scale at which the cap of the cube is `c`

Hop `t = ħ² / (2 m a²)`; the cap of the cube is `2 t a / ħ = ħ / (m a)`. This file proves,
algebraically, that the cap equals `c` exactly when `a = ħ / (m c)` (the reduced Compton
wavelength), that this length is `α · a₀`, and that the Bohr speed is `α c`, so that the 1s
runs at the fraction `α` of the cap.
-/

namespace NRS3Hidrogeno

variable {ħ m c e ε₀ : ℝ}

/-- The hop of the cube with cell side `a`. -/
noncomputable def hop (ħ m a : ℝ) : ℝ := ħ ^ 2 / (2 * m * a ^ 2)

/-- The speed cap of the cube: `2 t a / ħ`. -/
noncomputable def cap (ħ m a : ℝ) : ℝ := 2 * hop ħ m a * a / ħ

/-- Fine structure constant. -/
noncomputable def alpha (ħ c e ε₀ : ℝ) : ℝ := e ^ 2 / (4 * Real.pi * ε₀ * ħ * c)

/-- Bohr radius. -/
noncomputable def bohr (ħ m e ε₀ : ℝ) : ℝ := 4 * Real.pi * ε₀ * ħ ^ 2 / (m * e ^ 2)

lemma cap_eq (hħ : ħ ≠ 0) (hm : m ≠ 0) {a : ℝ} (ha : a ≠ 0) : cap ħ m a = ħ / (m * a) := by
  unfold cap hop; field_simp

/-- The cap is `c` exactly at the reduced Compton wavelength. -/
theorem cap_eq_c_iff (hħ : ħ ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) {a : ℝ} (ha : a ≠ 0) :
    cap ħ m a = c ↔ a = ħ / (m * c) := by
  rw [cap_eq hħ hm ha]
  constructor
  · intro h; field_simp at h ⊢; linarith
  · intro h; rw [h]; field_simp

/-- The reduced Compton wavelength is `α a₀`. -/
theorem compton_eq_alpha_bohr (hħ : ħ ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) (he : e ≠ 0)
    (hε : ε₀ ≠ 0) :
    ħ / (m * c) = alpha ħ c e ε₀ * bohr ħ m e ε₀ := by
  unfold alpha bohr
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- The Bohr speed `ħ / (m a₀)` is `α c`. -/
theorem bohr_speed (hħ : ħ ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) (he : e ≠ 0) (hε : ε₀ ≠ 0) :
    ħ / (m * bohr ħ m e ε₀) = alpha ħ c e ε₀ * c := by
  unfold alpha bohr
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- At the Compton scale the 1s runs at the fraction `α` of the cap of the cube. -/
theorem bohr_speed_over_cap (hħ : ħ ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) (he : e ≠ 0)
    (hε : ε₀ ≠ 0) :
    (ħ / (m * bohr ħ m e ε₀)) / cap ħ m (ħ / (m * c)) = alpha ħ c e ε₀ := by
  have ha : ħ / (m * c) ≠ 0 := div_ne_zero hħ (mul_ne_zero hm hc)
  have hcap : cap ħ m (ħ / (m * c)) = c := (cap_eq_c_iff hħ hm hc ha).2 rfl
  rw [hcap, bohr_speed hħ hm hc he hε]
  field_simp

end NRS3Hidrogeno

import Mathlib
import NRS3Hidrogeno.Escala
import NRS3Hidrogeno.Velocidad
import NRS3Hidrogeno.CuboEntero

/-!
# Scale and speed cap on the integer sites

`Escala` and `Velocidad` never used a half step: the cap `2 t a / ħ` and the Compton scale are
algebra, and the speed cap is a statement about the shifts `p ± e_i` of `ℤ³`. Here they meet the
integer box, whose closest site to the nucleus is at exactly one step `a`:

* the speed cap holds on every integer box, whatever its size;
* at the Compton scale `a = ħ / (m c)` the Coulomb energy of the closest site is `α m c²`;
* the Bohr radius is `1 / α` steps.
-/

namespace NRS3Hidrogeno

open Finset

/-- **The speed cap on the integer boxes**: `‖v_i ψ‖ ≤ ‖ψ‖ / a` for every state of the box of
half-side `M`, along every axis, for every `M`. -/
theorem vel_bound_cuboE (M : ℕ) (ψ : ℤ × ℤ × ℤ → ℂ) (hS : ∀ p ∉ cuboE M, ψ p = 0) (i : Fin 3)
    {a : ℝ} (ha : 0 < a) :
    ∑ p ∈ reach (cuboE M) i, ‖vel i (1 / (2 * a ^ 2)) a ψ p‖ ^ 2 ≤
      (1 / a) ^ 2 * ∑ q ∈ cuboE M, ‖ψ q‖ ^ 2 :=
  vel_bound_cube (cuboE M) ψ hS i ha

/-- The Coulomb constant `e² / (4 π ε₀)`. -/
noncomputable def coulombConst (e ε₀ : ℝ) : ℝ := e ^ 2 / (4 * Real.pi * ε₀)

/-- **At the Compton scale, the closest site has Coulomb energy `α m c²`.** -/
theorem coulomb_nearest_at_compton {ħ m c e ε₀ : ℝ} (hħ : ħ ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0)
    (hε : ε₀ ≠ 0) :
    coulombConst e ε₀ / (ħ / (m * c)) = alpha ħ c e ε₀ * (m * c ^ 2) := by
  unfold coulombConst alpha
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **The Bohr radius is `1 / α` steps** when the step is the reduced Compton wavelength. -/
theorem bohr_in_steps {ħ m c e ε₀ : ℝ} (hħ : ħ ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) (he : e ≠ 0)
    (hε : ε₀ ≠ 0) :
    bohr ħ m e ε₀ / (ħ / (m * c)) = 1 / alpha ħ c e ε₀ := by
  unfold bohr alpha
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end NRS3Hidrogeno

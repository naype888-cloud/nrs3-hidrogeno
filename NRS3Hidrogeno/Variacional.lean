import Mathlib
import NRS3Hidrogeno.Cubo
import NRS3Hidrogeno.Cinetica

/-!
# An upper bound for the ground energy of the cube

`groundEnergy` is the infimum of the energy over the unit states supported in the cube of
`(2M)³` cells (zero outside: the cube is finite and closed). It is bounded below, so every
trial state gives an upper bound. The trial state is the block of the `8` cells around the
origin corner, each with amplitude `1/√8`.
-/

namespace NRS3Hidrogeno

open Finset

/-- The energy form with every edge that touches the support. -/
noncomputable def energyFull (k a : ℝ) (S : Finset (ℤ × ℤ × ℤ)) (ψ : ℤ × ℤ × ℤ → ℝ) : ℝ :=
  kineticFull a S ψ + coulomb k a S ψ

/-- Unit states of the cube of `(2M)³` cells. -/
def Unit (M : ℕ) : Set (ℤ × ℤ × ℤ → ℝ) :=
  {ψ | (∀ p ∉ cubo M, ψ p = 0) ∧ ∑ p ∈ cubo M, ψ p ^ 2 = 1}

/-- The ground energy of the cube of `(2M)³` cells. -/
noncomputable def groundEnergy (k a : ℝ) (M : ℕ) : ℝ :=
  ⨅ ψ : Unit M, energyFull k a (cubo M) ψ

lemma kineticFull_nonneg {a : ℝ} (S : Finset (ℤ × ℤ × ℤ)) (ψ : ℤ × ℤ × ℤ → ℝ) :
    0 ≤ kineticFull a S ψ := by
  unfold kineticFull
  have : 0 ≤ 1 / (2 * a ^ 2) := by positivity
  exact mul_nonneg this (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun p _ => sq_nonneg _)

lemma energyFull_ge {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (M : ℕ) {ψ : ℤ × ℤ × ℤ → ℝ}
    (hψ : ψ ∈ Unit M) : -(k * (2 / (√3 * a))) ≤ energyFull k a (cubo M) ψ := by
  have h := coulomb_cubo_ge hk ha M ψ
  rw [hψ.2, mul_one] at h
  unfold energyFull
  linarith [kineticFull_nonneg (a := a) (cubo M) ψ]

lemma bddBelow {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (M : ℕ) :
    BddBelow (Set.range fun ψ : Unit M => energyFull k a (cubo M) ψ) :=
  ⟨-(k * (2 / (√3 * a))), by rintro _ ⟨ψ, rfl⟩; exact energyFull_ge hk ha M ψ.2⟩

/-- **Variational principle on the cube**: every unit state bounds the ground energy above. -/
theorem groundEnergy_le {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (M : ℕ) {ψ : ℤ × ℤ × ℤ → ℝ}
    (hψ : ψ ∈ Unit M) : groundEnergy k a M ≤ energyFull k a (cubo M) ψ :=
  ciInf_le (bddBelow hk ha M) ⟨ψ, hψ⟩

/-- The ground energy of the finite cube is bounded below. -/
theorem le_groundEnergy {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (M : ℕ) [Nonempty (Unit M)] :
    -(k * (2 / (√3 * a))) ≤ groundEnergy k a M :=
  le_ciInf fun ψ => energyFull_ge hk ha M ψ.2

end NRS3Hidrogeno

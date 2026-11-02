import Mathlib
import NRS3Hidrogeno.Prueba

/-!
# The ground energy of the cubes decreases and converges, and is never reached

Growing the cube can only lower the ground energy: a unit state of the cube of side `2 M` is a
unit state of the cube of side `2 (M + 1)`, with the same energy. The sequence is bounded
below (`le_groundEnergy`), so it converges to its infimum `E∞`, and every finite cube lies
above it. This is the shape of the Szegő limit: a limit of the finite cubes, below each of
them. That `E∞` is the Rydberg level is not proved here.
-/

namespace NRS3Hidrogeno

open Finset Filter
open scoped Topology

lemma cubo_subset_succ (M : ℕ) : cubo M ⊆ cubo (M + 1) := by
  intro p hp
  simp only [cubo, Finset.mem_product, Finset.mem_Ico] at hp ⊢
  push_cast
  omega

lemma edgeBase_mono {S S' : Finset (ℤ × ℤ × ℤ)} (h : S ⊆ S') (i : Fin 3) :
    edgeBase S i ⊆ edgeBase S' i :=
  Finset.union_subset_union h (Finset.image_subset_image h)

lemma kineticFull_congr (a : ℝ) {S S' : Finset (ℤ × ℤ × ℤ)} (h : S ⊆ S')
    (ψ : ℤ × ℤ × ℤ → ℝ) (hS : ∀ p ∉ S, ψ p = 0) :
    kineticFull a S' ψ = kineticFull a S ψ := by
  unfold kineticFull
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  symm
  refine Finset.sum_subset (edgeBase_mono h i) fun p _ hp => ?_
  have h1 : p ∉ S := fun hh => hp (Finset.mem_union_left _ hh)
  have h2 : p + axis i ∉ S := fun hh =>
    hp (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p + axis i, hh, by simp⟩))
  simp [hS p h1, hS _ h2]

lemma coulomb_congr (k a : ℝ) {S S' : Finset (ℤ × ℤ × ℤ)} (h : S ⊆ S')
    (ψ : ℤ × ℤ × ℤ → ℝ) (hS : ∀ p ∉ S, ψ p = 0) :
    coulomb k a S' ψ = coulomb k a S ψ := by
  unfold coulomb
  congr 1
  symm
  exact Finset.sum_subset h fun p _ hp => by simp [hS p hp]

lemma unit_succ {M : ℕ} {ψ : ℤ × ℤ × ℤ → ℝ} (hψ : ψ ∈ Unit M) : ψ ∈ Unit (M + 1) := by
  refine ⟨fun p hp => hψ.1 p fun hh => hp (cubo_subset_succ M hh), ?_⟩
  rw [← hψ.2]
  exact (Finset.sum_subset (cubo_subset_succ M) fun p _ hp => by
    simp [hψ.1 p hp]).symm

/-- A larger cube has a lower (or equal) ground energy. -/
theorem groundEnergy_succ_le {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) {M : ℕ} (hM : 1 ≤ M) :
    groundEnergy k a (M + 1) ≤ groundEnergy k a M := by
  have : Nonempty (Unit M) := ⟨⟨trial, trial_unit hM⟩⟩
  refine le_ciInf fun ψ => ?_
  have h := groundEnergy_le hk ha (M + 1) (unit_succ ψ.2)
  have e : energyFull k a (cubo (M + 1)) ψ = energyFull k a (cubo M) ψ := by
    unfold energyFull
    rw [kineticFull_congr a (cubo_subset_succ M) ψ ψ.2.1,
      coulomb_congr k a (cubo_subset_succ M) ψ ψ.2.1]
  rwa [e] at h

/-- The ground energies of the cubes of side `2 (n + 1)`. -/
noncomputable def levels (k a : ℝ) (n : ℕ) : ℝ := groundEnergy k a (n + 1)

/-- The limit of the finite cubes: the infimum of their ground energies. -/
noncomputable def limitEnergy (k a : ℝ) : ℝ := ⨅ n, levels k a n

lemma levels_antitone {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) : Antitone (levels k a) :=
  antitone_nat_of_succ_le fun n => groundEnergy_succ_le hk ha (by omega)

lemma levels_bddBelow {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) : BddBelow (Set.range (levels k a)) := by
  refine ⟨-(k * (2 / (√3 * a))), ?_⟩
  rintro _ ⟨n, rfl⟩
  have : Nonempty (Unit (n + 1)) := ⟨⟨trial, trial_unit (by omega)⟩⟩
  exact le_groundEnergy hk ha (n + 1)

/-- **The cubes converge**: the ground energy of the cube of side `2 (n + 1)` tends to
`limitEnergy`, from above. -/
theorem tendsto_levels {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) :
    Tendsto (levels k a) atTop (𝓝 (limitEnergy k a)) :=
  tendsto_atTop_ciInf (levels_antitone hk ha) (levels_bddBelow hk ha)

/-- Every finite cube lies above the limit. -/
theorem limitEnergy_le_levels {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (n : ℕ) :
    limitEnergy k a ≤ levels k a n :=
  ciInf_le (levels_bddBelow hk ha) n

/-- The limit is below the trial block, and above `-2 k / (√3 a)`. -/
theorem limitEnergy_bounds {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) :
    -(k * (2 / (√3 * a))) ≤ limitEnergy k a ∧
      limitEnergy k a ≤ 3 / (2 * a ^ 2) - k * (2 / (√3 * a)) := by
  refine ⟨le_ciInf fun n => ?_, (limitEnergy_le_levels hk ha 0).trans ?_⟩
  · have : Nonempty (Unit (n + 1)) := ⟨⟨trial, trial_unit (by omega)⟩⟩
    exact le_groundEnergy hk ha (n + 1)
  · exact groundEnergy_le_block hk ha (M := 0 + 1) (by omega)

end NRS3Hidrogeno

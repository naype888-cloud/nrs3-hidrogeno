import Mathlib
import NRS3Hidrogeno.CuboEntero

/-!
# The ground energy of the integer boxes decreases and converges, and is never reached

A unit state of the box of half-side `M` is a unit state of the box of half-side `M + 1`, with the
same energy: growing the box can only lower the ground energy. The sequence is bounded below by
`-2 k²` (Hardy's inequality on the integer sites, `le_groundE_hardy`), so it converges to its
infimum `E∞`, and every finite box lies above it. The bound does not depend on the box: a box of
`10⁹` sites per axis is covered as much as a small one. That `E∞` is the Rydberg level is not
proved here.
-/

namespace NRS3Hidrogeno

open Finset Filter
open scoped Topology

noncomputable section

lemma cuboE_subset_succ (M : ℕ) : cuboE M ⊆ cuboE (M + 1) := by
  intro p hp
  simp only [cuboE, Finset.mem_erase, Finset.mem_product, Finset.mem_Icc] at hp ⊢
  obtain ⟨h0, ⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := hp
  refine ⟨h0, ?_⟩
  push_cast
  omega

lemma edgeBase_mono {S S' : Finset (ℤ × ℤ × ℤ)} (h : S ⊆ S') (i : Fin 3) :
    edgeBase S i ⊆ edgeBase S' i :=
  Finset.union_subset_union h (Finset.image_subset_image h)

/-- Enlarging the support does not change the kinetic form of a state that vanishes outside it. -/
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

lemma coulombE_congr (k a : ℝ) {S S' : Finset (ℤ × ℤ × ℤ)} (h : S ⊆ S')
    (ψ : ℤ × ℤ × ℤ → ℝ) (hS : ∀ p ∉ S, ψ p = 0) :
    coulombE k a S' ψ = coulombE k a S ψ := by
  unfold coulombE
  congr 1
  symm
  exact Finset.sum_subset h fun p _ hp => by simp [hS p hp]

lemma unitE_succ {M : ℕ} {ψ : ℤ × ℤ × ℤ → ℝ} (hψ : ψ ∈ UnitE M) : ψ ∈ UnitE (M + 1) := by
  refine ⟨fun p hp => hψ.1 p fun hh => hp (cuboE_subset_succ M hh), ?_⟩
  rw [← hψ.2]
  exact (Finset.sum_subset (cuboE_subset_succ M) fun p _ hp => by
    simp [hψ.1 p hp]).symm

/-- A larger box has a lower (or equal) ground energy. -/
theorem groundE_succ_le {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) {M : ℕ} (hM : 1 ≤ M) :
    groundE k a (M + 1) ≤ groundE k a M := by
  have : Nonempty (UnitE M) := ⟨⟨trialE, trialE_unit hM⟩⟩
  refine le_ciInf fun ψ => ?_
  have h := groundE_le hk ha (M + 1) (unitE_succ ψ.2)
  have e : energyE k a (cuboE (M + 1)) ψ = energyE k a (cuboE M) ψ := by
    unfold energyE
    rw [kineticFull_congr a (cuboE_subset_succ M) ψ ψ.2.1,
      coulombE_congr k a (cuboE_subset_succ M) ψ ψ.2.1]
  rwa [e] at h

/-- The ground energies of the boxes of half-side `n + 1`. -/
def levelsE (k a : ℝ) (n : ℕ) : ℝ := groundE k a (n + 1)

/-- The limit of the finite boxes: the infimum of their ground energies. -/
def limitE (k a : ℝ) : ℝ := ⨅ n, levelsE k a n

lemma levelsE_antitone {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) : Antitone (levelsE k a) :=
  antitone_nat_of_succ_le fun n => groundE_succ_le hk ha (by omega)

lemma levelsE_bddBelow {k a : ℝ} (ha : 0 < a) : BddBelow (Set.range (levelsE k a)) := by
  refine ⟨-(k ^ 2 / (2 * (1 / 4))), ?_⟩
  rintro _ ⟨n, rfl⟩
  exact le_groundE_hardy ha (M := n + 1) (by omega)

/-- **The boxes converge**: the ground energy of the box of half-side `n + 1` tends to
`limitE`, from above. -/
theorem tendsto_levelsE {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) :
    Tendsto (levelsE k a) atTop (𝓝 (limitE k a)) :=
  tendsto_atTop_ciInf (levelsE_antitone hk ha) (levelsE_bddBelow ha)

/-- Every finite box lies above the limit. -/
theorem limitE_le_levels {k a : ℝ} (ha : 0 < a) (n : ℕ) : limitE k a ≤ levelsE k a n :=
  ciInf_le (levelsE_bddBelow ha) n

/-- **The limit lies below the trial site and above both lower bounds**: `-2 k²`, which does not
depend on `a`, and `-k / a`, which does. -/
theorem limitE_bounds {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) :
    max (-(k ^ 2 / (2 * (1 / 4)))) (-(k / a)) ≤ limitE k a ∧
      limitE k a ≤ 3 / a ^ 2 - k / a := by
  refine ⟨max_le (le_ciInf fun n => le_groundE_hardy ha (M := n + 1) (by omega))
    (le_ciInf fun n => ?_), (limitE_le_levels ha 0).trans ?_⟩
  · have : Nonempty (UnitE (n + 1)) := ⟨⟨trialE, trialE_unit (by omega)⟩⟩
    exact le_groundE hk ha (n + 1)
  · exact groundE_le_trial hk ha (M := 0 + 1) (by omega)

end

end NRS3Hidrogeno

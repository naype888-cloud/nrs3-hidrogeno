import Mathlib
import NRS3Hidrogeno.Hilbert.Hidrogeno

/-!
# The indicator state of a region

For a non-empty set `B` of sites of a graph, the state `ψ_B = |B|^(-1/2) 1_B` has a Rayleigh quotient
`t · (edges leaving B) / |B| + (Σ_{p ∈ B} V p) / |B|`. Every region of the graph bounds the ground
energy above.

## Main results

- `edgeForm_indicator` : the edge form of `ψ_B` is the number of edges leaving `B` over `|B|`.
- `groundEnergy_le_region` : `groundEnergy ≤ t · |∂B| / |B| + (Σ_B V) / |B|`.
-/

namespace NRS3Hidrogeno.Hilbert

open scoped InnerProductSpace
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj]

/-- The number of edges that leave `B`, counted from the inside. -/
def outEdges (B : Finset ι) : ℕ :=
  (Finset.univ.filter fun e : ι × ι => e.1 ∈ B ∧ e.2 ∉ B ∧ G.Adj e.1 e.2).card

/-- The amplitude `|B|^(-1/2)` of the normalised indicator. -/
noncomputable def amp (B : Finset ι) : ℝ := ((B.card : ℝ) ^ (1 / 2 : ℝ))⁻¹

omit [Fintype ι] [DecidableEq ι] in
lemma amp_sq (B : Finset ι) (hB : B.Nonempty) : amp B ^ 2 = 1 / B.card := by
  have h : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  unfold amp
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul h.le]
  norm_num

/-- The normalised indicator of `B`. -/
noncomputable def indicator (B : Finset ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun i => if i ∈ B then (amp B : ℂ) else 0

omit [Fintype ι] in
lemma indicator_apply (B : Finset ι) (i : ι) :
    (indicator B).ofLp i = if i ∈ B then (amp B : ℂ) else 0 := rfl

lemma norm_indicator {B : Finset ι} (hB : B.Nonempty) : ‖indicator B‖ = 1 := by
  have h : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hsq : ‖indicator B‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    have : ∀ i, ‖(indicator B).ofLp i‖ ^ 2 = if i ∈ B then 1 / (B.card : ℝ) else 0 := fun i => by
      rw [indicator_apply]
      split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, amp_sq B hB]
      · simp
    simp_rw [this]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul]
    field_simp
  nlinarith [norm_nonneg (indicator B)]

omit [Fintype ι] [DecidableEq ι] in
lemma amp_nonneg (B : Finset ι) : 0 ≤ amp B := by
  unfold amp; positivity

/-- **The edge form of the indicator is the number of edges leaving `B` over `|B|`.** -/
theorem edgeForm_indicator {B : Finset ι} (hB : B.Nonempty) :
    edgeForm G (indicator B) = outEdges G B / B.card := by
  have key : ∀ i j, (if G.Adj i j then ‖(indicator B).ofLp i - (indicator B).ofLp j‖ ^ 2 else 0) =
      (if i ∈ B ∧ j ∉ B ∧ G.Adj i j then amp B ^ 2 else 0) +
        (if j ∈ B ∧ i ∉ B ∧ G.Adj j i then amp B ^ 2 else 0) := by
    intro i j
    have h0 := amp_nonneg B
    simp only [G.adj_comm j i]
    by_cases hi : i ∈ B <;> by_cases hj : j ∈ B <;> by_cases ha : G.Adj i j <;>
      simp [indicator_apply, hi, hj, ha, Complex.norm_real, abs_of_nonneg h0]
  have h1 : ∑ i, ∑ j, (if i ∈ B ∧ j ∉ B ∧ G.Adj i j then amp B ^ 2 else 0) =
      outEdges G B * amp B ^ 2 := by
    rw [← Fintype.sum_prod_type' (fun i j => if i ∈ B ∧ j ∉ B ∧ G.Adj i j then amp B ^ 2 else 0),
      ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rfl
  have h2 : ∑ i, ∑ j, (if j ∈ B ∧ i ∉ B ∧ G.Adj j i then amp B ^ 2 else 0) =
      ∑ i, ∑ j, (if i ∈ B ∧ j ∉ B ∧ G.Adj i j then amp B ^ 2 else 0) := Finset.sum_comm
  unfold edgeForm
  simp_rw [key, Finset.sum_add_distrib]
  rw [h2, h1, amp_sq B hB]
  ring

/-- **Every region bounds the ground energy above.** -/
theorem groundEnergy_le_region {B : Finset ι} (hB : B.Nonempty) (t : ℝ) (V : ι → ℝ) :
    groundEnergy (hamiltonian G t V) ⊤ ≤
      t * (outEdges G B / B.card) + (∑ i ∈ B, V i) / B.card := by
  have h := groundEnergy_le (hamiltonian G t V) ⊤ (Submodule.mem_top : indicator B ∈ ⊤)
    (norm_indicator hB)
  rw [rayleigh_hamiltonian, edgeForm_indicator G hB] at h
  have hv : ∑ i, V i * ‖(indicator B).ofLp i‖ ^ 2 = (∑ i ∈ B, V i) / B.card := by
    have : ∀ i, V i * ‖(indicator B).ofLp i‖ ^ 2 = if i ∈ B then V i / B.card else 0 := fun i => by
      rw [indicator_apply]
      split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, amp_sq B hB]; ring
      · simp
    simp_rw [this]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_div]
  rwa [hv] at h

end NRS3Hidrogeno.Hilbert

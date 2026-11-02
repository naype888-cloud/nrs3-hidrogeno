import Mathlib
import NRS3Hidrogeno.Hilbert.Velocidad

/-!
# A Coulomb centre on a hopping Hamiltonian

The potential is `V p = wall p - k / r p`: `wall ≥ 0` is the wall of the box (the cube with zero
outside is the graph Laplacian plus a non-negative potential on the cells at the border), `r p` is
the distance of the site `p` from the nucleus and `k ≥ 0` the strength. If the nucleus is at least
at `ρ` from every site, the ground energy is at least `-k / ρ`, whatever the graph.
-/

namespace NRS3Hidrogeno.Hilbert

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj]

/-- The potential of a Coulomb centre inside a box. -/
noncomputable def coulombBox (k : ℝ) (r wall : ι → ℝ) : ι → ℝ := fun p => wall p - k / r p

/-- **The ground energy of a Coulomb centre on any hopping graph is at least `-k / ρ`.** -/
theorem groundEnergy_coulomb_ge {t k ρ : ℝ} (ht : 0 ≤ t) (hk : 0 ≤ k) (hρ : 0 < ρ)
    {r wall : ι → ℝ} (hr : ∀ p, ρ ≤ r p) (hw : ∀ p, 0 ≤ wall p)
    (W : Submodule ℂ (EuclideanSpace ℂ ι)) (hne : Nonempty (UnitIn W)) :
    -(k / ρ) ≤ groundEnergy (hamiltonian G t (coulombBox k r wall)) W := by
  refine groundEnergy_ge_potential G ht (fun p => ?_) W hne
  have h1 : k / r p ≤ k / ρ := div_le_div_of_nonneg_left hk hρ (hr p)
  unfold coulombBox
  linarith [hw p]

end NRS3Hidrogeno.Hilbert

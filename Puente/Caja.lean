import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import NavaRobertsonCertificados.D50k_WordDefectBand

/-!
# Bridge: the adjacency of the cube graph is `ρ (T_x + T_y + T_z)` of `D37`

The graph of the cube of `PhyslibAlpha.CondensedMatter.LatticeModels.BoxGraph` is the box product
of three paths. Its adjacency operator is the sum over the three axes of the hop of the path,
`A_d = ρ_d T_d` (`D3`), lifted to the axis (`D37`). So the hopping of the Hamiltonian of that cube is
`ρ_x T_x + ρ_y T_y + ρ_z T_z`, and the words of `D50g` are words in these three hops.

Compiled inside the corpus (it does not share a Mathlib with the mosaic):
`cd nava-robertson-schrodinger && lake env lean ../nrs3-hidrogeno/Puente/Caja.lean`.
-/

open SimpleGraph TransportPosition PathGraph3DNRS PathGraph3D

namespace Puente

open Classical in
/-- **The adjacency operator of the cube graph is `ρ_x T_x + ρ_y T_y + ρ_z T_z`.** -/
theorem adjacency_cube {dx dy dz : ℕ} (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    Matrix.toEuclideanLin
        ((pathGraph dx □ (pathGraph dy □ pathGraph dz)).adjMatrix ℂ) =
      (rho dx : ℂ) • TX (dx := dx) (dy := dy) (dz := dz) +
        (rho dy : ℂ) • TY (dx := dx) (dy := dy) (dz := dz) +
        (rho dz : ℂ) • TZ (dx := dx) (dy := dy) (dz := dz) := by
  have hρ : ∀ d : ℕ, 2 ≤ d → (rho d : ℂ) ≠ 0 := by
    intro d hd
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have h1 : 0 < Real.cos (Real.pi / ((d : ℝ) + 1)) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · have : 0 < Real.pi / ((d : ℝ) + 1) := by positivity
        have := Real.pi_pos
        linarith
      · rw [div_lt_iff₀ (by positivity)]
        nlinarith [Real.pi_pos]
    have : rho d ≠ 0 := by unfold rho; positivity
    exact_mod_cast this
  have hM : (pathGraph dx □ (pathGraph dy □ pathGraph dz)).adjMatrix ℂ =
      (rho dx : ℂ) • liftAlong (eX dx dy dz) (Td dx) +
        (rho dy : ℂ) • liftAlong (eY dx dy dz) (Td dy) +
        (rho dz : ℂ) • liftAlong (eZ dx dy dz) (Td dz) := by
    have hT : ∀ d : ℕ, 2 ≤ d → ∀ i j : Fin d, (rho d : ℂ) * Td d i j = Ad d i j := by
      intro d hd i j
      have := hρ d hd
      unfold Td
      field_simp
    ext ⟨x, y, z⟩ ⟨x', y', z'⟩
    simp only [Matrix.add_apply, Matrix.smul_apply, liftAlong, Matrix.of_apply, eX, eY, eZ,
      Equiv.refl_apply, Equiv.coe_fn_mk, smul_eq_mul, ← mul_assoc, hT dx hx, hT dy hy, hT dz hz,
      Ad, MinStep, SimpleGraph.adjMatrix_apply, SimpleGraph.boxProd_adj, pathGraph_adj,
      Prod.mk.injEq]
    by_cases a1 : x = x' <;> by_cases a2 : y = y' <;> by_cases a3 : z = z' <;> simp_all
  simp only [TX, TY, TZ, ← map_smul, ← map_add, hM]

end Puente

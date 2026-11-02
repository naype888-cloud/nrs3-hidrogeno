import Mathlib
import NRS3Hidrogeno.Cinetica

/-!
# The kinetic form of the integer cube is the quadratic form of the cube graph

The cube of `D37` is `Fin dx × Fin dy × Fin dz` with the graph `pathGraph dx □ (pathGraph dy □
pathGraph dz)`. Placed in `ℤ³` by `boxEmb`, two sites are adjacent exactly when they differ by an
axis step. Hence, for every `ψ` supported in the box, the hop form `adjForm` of `Cinetica` (twice the
sum over the axis edges of `ψ(p) ψ(p + e_i)`) is the quadratic form `⟨ψ, A ψ⟩` of the adjacency
matrix `A` of the cube graph (`adjForm_boxSet`). With `kineticFull_eq` the kinetic form is
`⟨ψ, (6 - A) ψ⟩ / (2 a²)`, and `A = ρ_x T_x + ρ_y T_y + ρ_z T_z` is `Puente.adjacency_cube`.
-/

namespace NRS3Hidrogeno

open Finset SimpleGraph

noncomputable section

open scoped Classical

variable (dx dy dz : ℕ)

/-- The cube `Fin dx × Fin dy × Fin dz` placed in the sites `ℤ³`. -/
def boxEmb : Fin dx × Fin dy × Fin dz → ℤ × ℤ × ℤ :=
  fun s => ((s.1.val : ℤ), (s.2.1.val : ℤ), (s.2.2.val : ℤ))

lemma boxEmb_injective : Function.Injective (boxEmb dx dy dz) := by
  intro s t h
  simp only [boxEmb, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;> omega

/-- The box as a set of sites. -/
def boxSet : Finset (ℤ × ℤ × ℤ) := Finset.univ.image (boxEmb dx dy dz)

/-- The graph of the cube: the box product of three paths. -/
abbrev cubeG : SimpleGraph (Fin dx × Fin dy × Fin dz) :=
  pathGraph dx □ (pathGraph dy □ pathGraph dz)

variable {dx dy dz}

set_option maxHeartbeats 4000000 in
/-- **Adjacency in the cube graph is an axis step**: the indicator of the adjacency is the sum, over
the three axes, of the indicators of `t = s + e_i` and `s = t + e_i`. -/
lemma indicator_adj (s t : Fin dx × Fin dy × Fin dz) :
    (if (cubeG dx dy dz).Adj s t then (1 : ℝ) else 0) =
      ∑ i : Fin 3, ((if boxEmb dx dy dz t = boxEmb dx dy dz s + axis i then 1 else 0) +
        (if boxEmb dx dy dz s = boxEmb dx dy dz t + axis i then 1 else 0)) := by
  rw [Fin.sum_univ_three]
  simp only [boxEmb, axis, Prod.mk_add_mk, boxProd_adj, pathGraph_adj,
    Prod.ext_iff, Fin.ext_iff]
  split_ifs <;> first | omega | norm_num

/-- Summing a function supported in the box over the box, against one site. -/
lemma sum_ind (ψ : ℤ × ℤ × ℤ → ℝ) (hψ : ∀ p ∉ boxSet dx dy dz, ψ p = 0) (q : ℤ × ℤ × ℤ) :
    ∑ t : Fin dx × Fin dy × Fin dz,
      (if boxEmb dx dy dz t = q then ψ (boxEmb dx dy dz t) else 0) = ψ q := by
  by_cases hq : q ∈ boxSet dx dy dz
  · obtain ⟨t0, _, rfl⟩ := Finset.mem_image.mp hq
    rw [Finset.sum_eq_single t0]
    · simp
    · intro t _ ht
      have : boxEmb dx dy dz t ≠ boxEmb dx dy dz t0 := fun h => ht (boxEmb_injective _ _ _ h)
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ t0) h
  · rw [hψ q hq]
    refine Finset.sum_eq_zero fun t _ => ?_
    have : boxEmb dx dy dz t ≠ q := fun h =>
      hq (h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ t))
    simp [this]

lemma sum_box_eq (F : ℤ × ℤ × ℤ → ℝ) :
    ∑ s : Fin dx × Fin dy × Fin dz, F (boxEmb dx dy dz s) = ∑ p ∈ boxSet dx dy dz, F p := by
  rw [boxSet, Finset.sum_image (fun s _ t _ h => boxEmb_injective _ _ _ h)]

/-- The hop form seen from the box: `Σ_s ψ(s) ψ(s - e_i)` equals `Σ_s ψ(s) ψ(s + e_i)`. -/
lemma sum_shift_box (ψ : ℤ × ℤ × ℤ → ℝ) (hψ : ∀ p ∉ boxSet dx dy dz, ψ p = 0) (i : Fin 3) :
    ∑ s : Fin dx × Fin dy × Fin dz, ψ (boxEmb dx dy dz s) * ψ (boxEmb dx dy dz s - axis i) =
      ∑ s : Fin dx × Fin dy × Fin dz, ψ (boxEmb dx dy dz s) * ψ (boxEmb dx dy dz s + axis i) := by
  rw [sum_box_eq (fun p => ψ p * ψ (p - axis i)), sum_box_eq (fun p => ψ p * ψ (p + axis i))]
  have h1 := sum_edgeBase_shift (boxSet dx dy dz) (fun q => ψ q * ψ (q - axis i))
    (fun p hp => by simp [hψ p hp]) i
  have h2 := sum_edgeBase_self (boxSet dx dy dz) (fun p => ψ p * ψ (p + axis i))
    (fun p hp => by simp [hψ p hp]) i
  simp only [add_sub_cancel_right] at h1
  rw [← h1, ← h2]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

/-- **The hop form of the integer cube is the quadratic form of the cube graph.** For every `ψ`
supported in the box, `adjForm ψ = ⟨ψ, A ψ⟩`, with `A` the adjacency matrix of
`pathGraph dx □ (pathGraph dy □ pathGraph dz)`. -/
theorem adjForm_boxSet (ψ : ℤ × ℤ × ℤ → ℝ) (hψ : ∀ p ∉ boxSet dx dy dz, ψ p = 0) :
    adjForm (boxSet dx dy dz) ψ =
      ∑ s : Fin dx × Fin dy × Fin dz, ∑ t : Fin dx × Fin dy × Fin dz,
        (if (cubeG dx dy dz).Adj s t then (1 : ℝ) else 0) *
          (ψ (boxEmb dx dy dz s) * ψ (boxEmb dx dy dz t)) := by
  have hL : ∀ i : Fin 3, ∑ p ∈ edgeBase (boxSet dx dy dz) i, 2 * (ψ p * ψ (p + axis i)) =
      ∑ s : Fin dx × Fin dy × Fin dz,
        2 * (ψ (boxEmb dx dy dz s) * ψ (boxEmb dx dy dz s + axis i)) := by
    intro i
    rw [sum_edgeBase_self (boxSet dx dy dz) (fun p => 2 * (ψ p * ψ (p + axis i)))
      (fun p hp => by simp [hψ p hp]) i]
    exact (sum_box_eq (fun p => 2 * (ψ p * ψ (p + axis i)))).symm
  have hR : ∀ s : Fin dx × Fin dy × Fin dz,
      ∑ t : Fin dx × Fin dy × Fin dz, (if (cubeG dx dy dz).Adj s t then (1 : ℝ) else 0) *
          (ψ (boxEmb dx dy dz s) * ψ (boxEmb dx dy dz t)) =
        ∑ i : Fin 3, (ψ (boxEmb dx dy dz s) * ψ (boxEmb dx dy dz s + axis i) +
          ψ (boxEmb dx dy dz s) * ψ (boxEmb dx dy dz s - axis i)) := by
    intro s
    simp_rw [indicator_adj, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 := sum_ind ψ hψ (boxEmb dx dy dz s + axis i)
    have e2 := sum_ind ψ hψ (boxEmb dx dy dz s - axis i)
    have c2 : ∀ t : Fin dx × Fin dy × Fin dz,
        (boxEmb dx dy dz s = boxEmb dx dy dz t + axis i) ↔
          (boxEmb dx dy dz t = boxEmb dx dy dz s - axis i) := fun t => by
      rw [eq_sub_iff_add_eq]
      exact eq_comm
    simp_rw [add_mul, Finset.sum_add_distrib, c2]
    have k1 : ∀ t : Fin dx × Fin dy × Fin dz,
        (if boxEmb dx dy dz t = boxEmb dx dy dz s + axis i then (1 : ℝ) else 0) *
          (ψ (boxEmb dx dy dz s) * ψ (boxEmb dx dy dz t)) =
        ψ (boxEmb dx dy dz s) *
          (if boxEmb dx dy dz t = boxEmb dx dy dz s + axis i then ψ (boxEmb dx dy dz t) else 0) :=
      fun t => by split_ifs <;> simp
    have k2 : ∀ t : Fin dx × Fin dy × Fin dz,
        (if boxEmb dx dy dz t = boxEmb dx dy dz s - axis i then (1 : ℝ) else 0) *
          (ψ (boxEmb dx dy dz s) * ψ (boxEmb dx dy dz t)) =
        ψ (boxEmb dx dy dz s) *
          (if boxEmb dx dy dz t = boxEmb dx dy dz s - axis i then ψ (boxEmb dx dy dz t) else 0) :=
      fun t => by split_ifs <;> simp
    simp_rw [k1, k2, ← Finset.mul_sum, e1, e2]
  unfold adjForm
  rw [Finset.sum_congr rfl fun i _ => hL i, Finset.sum_congr rfl fun s _ => hR s]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_add_distrib, sum_shift_box ψ hψ i, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **The kinetic form of the integer cube is `⟨ψ, (6 - A) ψ⟩ / (2 a²)`**, with `A` the adjacency
matrix of the cube graph `pathGraph dx □ (pathGraph dy □ pathGraph dz)` of `D37`. -/
theorem kineticFull_boxSet (a : ℝ) (ψ : ℤ × ℤ × ℤ → ℝ)
    (hψ : ∀ p ∉ boxSet dx dy dz, ψ p = 0) :
    kineticFull a (boxSet dx dy dz) ψ =
      (1 / (2 * a ^ 2)) * (6 * ∑ p ∈ boxSet dx dy dz, ψ p ^ 2 -
        ∑ s : Fin dx × Fin dy × Fin dz, ∑ t : Fin dx × Fin dy × Fin dz,
          (if (cubeG dx dy dz).Adj s t then (1 : ℝ) else 0) *
            (ψ (boxEmb dx dy dz s) * ψ (boxEmb dx dy dz t))) := by
  rw [kineticFull_eq a _ ψ hψ, adjForm_boxSet ψ hψ]

end

end NRS3Hidrogeno

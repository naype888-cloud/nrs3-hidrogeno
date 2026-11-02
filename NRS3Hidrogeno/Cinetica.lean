import Mathlib
import NRS3Hidrogeno.Sitios

/-!
# The kinetic form of the cube is `⟨ψ, (6 - A) ψ⟩ / (2 a²)`

`A` is the adjacency of the axis hops. Over every edge that touches the support, the sum of
the squared differences is `6 ‖ψ‖² - ⟨ψ, A ψ⟩`.
-/

namespace NRS3Hidrogeno

open Finset

/-- The cells whose axis edge towards `p + e_i` touches the support `S`. -/
def edgeBase (S : Finset (ℤ × ℤ × ℤ)) (i : Fin 3) : Finset (ℤ × ℤ × ℤ) :=
  S ∪ S.image (· - axis i)

lemma sum_edgeBase_self (S : Finset (ℤ × ℤ × ℤ)) (g : ℤ × ℤ × ℤ → ℝ) (hg : ∀ p ∉ S, g p = 0)
    (i : Fin 3) : ∑ p ∈ edgeBase S i, g p = ∑ p ∈ S, g p :=
  (Finset.sum_subset Finset.subset_union_left (fun p _ hp => hg p hp)).symm

lemma sum_edgeBase_shift (S : Finset (ℤ × ℤ × ℤ)) (g : ℤ × ℤ × ℤ → ℝ) (hg : ∀ p ∉ S, g p = 0)
    (i : Fin 3) : ∑ p ∈ edgeBase S i, g (p + axis i) = ∑ p ∈ S, g p := by
  have hsub : S.image (· - axis i) ⊆ edgeBase S i := Finset.subset_union_right
  rw [← Finset.sum_subset hsub, Finset.sum_image]
  · simp
  · intro x _ y _ h; simpa using h
  · intro p _ hp
    have : p + axis i ∉ S := by
      intro h
      exact hp (Finset.mem_image.mpr ⟨p + axis i, h, by simp⟩)
    exact hg _ this

/-- The hop form `⟨ψ, A ψ⟩`: twice the sum over the axis edges of `ψ(p) ψ(p + e_i)`. -/
def adjForm (S : Finset (ℤ × ℤ × ℤ)) (ψ : ℤ × ℤ × ℤ → ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ p ∈ edgeBase S i, 2 * (ψ p * ψ (p + axis i))

/-- The kinetic form over every edge that touches the support. -/
noncomputable def kineticFull (a : ℝ) (S : Finset (ℤ × ℤ × ℤ)) (ψ : ℤ × ℤ × ℤ → ℝ) : ℝ :=
  (1 / (2 * a ^ 2)) * ∑ i : Fin 3, ∑ p ∈ edgeBase S i, (ψ (p + axis i) - ψ p) ^ 2

/-- **The kinetic form is `⟨ψ, (6 - A) ψ⟩ / (2 a²)`.** -/
theorem kineticFull_eq (a : ℝ) (S : Finset (ℤ × ℤ × ℤ)) (ψ : ℤ × ℤ × ℤ → ℝ)
    (hS : ∀ p ∉ S, ψ p = 0) :
    kineticFull a S ψ = (1 / (2 * a ^ 2)) * (6 * ∑ p ∈ S, ψ p ^ 2 - adjForm S ψ) := by
  have hg : ∀ p ∉ S, ψ p ^ 2 = 0 := fun p hp => by simp [hS p hp]
  have key : ∀ i : Fin 3, ∑ p ∈ edgeBase S i, (ψ (p + axis i) - ψ p) ^ 2 =
      2 * ∑ p ∈ S, ψ p ^ 2 - ∑ p ∈ edgeBase S i, 2 * (ψ p * ψ (p + axis i)) := by
    intro i
    have h1 := sum_edgeBase_shift S (fun p => ψ p ^ 2) hg i
    have h2 := sum_edgeBase_self S (fun p => ψ p ^ 2) hg i
    have h3 : ∑ p ∈ edgeBase S i, (ψ (p + axis i) - ψ p) ^ 2 =
        ∑ p ∈ edgeBase S i, ψ (p + axis i) ^ 2 + ∑ p ∈ edgeBase S i, ψ p ^ 2
          - ∑ p ∈ edgeBase S i, 2 * (ψ p * ψ (p + axis i)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [h3]
    rw [h1, h2]; ring
  unfold kineticFull adjForm
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_sub_distrib]
  rw [Fin.sum_univ_three]
  ring

end NRS3Hidrogeno

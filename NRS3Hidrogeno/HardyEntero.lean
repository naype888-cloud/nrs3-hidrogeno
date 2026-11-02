import Mathlib
import NRS3Hidrogeno.HardyCampo

/-!
# Hardy on integer sites: the nucleus cell excluded, no half steps

The electron sits on the integer sites `p ∈ ℤ³ \ {0}`; the cell `0` is the nucleus and carries no
position. The distance to the nucleus is `√(p₁² + p₂² + p₃²) ≥ 1`. For every state `ψ` supported in
a finite set with `ψ 0 = 0`,
`(1/4) Σ ψ² / r² ≤ Σ over the axis edges of the squared differences`:
for every finite box, with the constant `1/4`. The field on the edges is `κ = (1/4) m / (m² + q + 1)`, with
`m` the coordinate of the midpoint of the edge along its axis and `q` the squared distance of the
other two coordinates. The proof is a chord argument (`phi` is concave in `x²`) followed by a
polynomial in one variable with positive coefficients.
-/

namespace NRS3Hidrogeno

open Finset

noncomputable section

/-- The field on an edge with midpoint coordinate `m` and transverse square distance `q`. -/
def kk (m q : ℝ) : ℝ := (1 / 4) * m / (m ^ 2 + q + 1)

/-- The weight that the field produces on one axis. -/
def fax (x q : ℝ) : ℝ :=
  2 * kk (x + 1 / 2) q - 2 * kk (x - 1 / 2) q - 2 * kk (x + 1 / 2) q ^ 2 -
    2 * kk (x - 1 / 2) q ^ 2

/-- The same weight written in `u = x²` and `s = x² + q + 5/4`. -/
def phi (s u : ℝ) : ℝ :=
  3 / 4 - (s ^ 2 / 4 - 1 / 16) / (s ^ 2 - u) - (s ^ 2 * (s - 1 / 2) ^ 2 / 2) / (s ^ 2 - u) ^ 2

lemma fax_eq (x q : ℝ) (hq : 0 ≤ q) : fax x q = phi (x ^ 2 + q + 5 / 4) (x ^ 2) := by
  have e1 : (x + 1 / 2) ^ 2 + q + 1 = (x ^ 2 + q + 5 / 4) + x := by ring
  have e2 : (x - 1 / 2) ^ 2 + q + 1 = (x ^ 2 + q + 5 / 4) - x := by ring
  unfold fax kk phi
  rw [e1, e2]
  generalize hs : x ^ 2 + q + 5 / 4 = s
  have hp : 0 < s + x := by nlinarith [sq_nonneg (x + 1 / 2)]
  have hm : 0 < s - x := by nlinarith [sq_nonneg (x - 1 / 2)]
  have e3 : s ^ 2 - x ^ 2 = (s + x) * (s - x) := by ring
  rw [e3]
  have := hp.ne'
  have := hm.ne'
  field_simp
  ring

lemma chord1 {m M d : ℝ} (hm : 0 < m) (h1 : m ≤ d) (h2 : d ≤ M) :
    1 / d ≤ 1 / m + 1 / M - d / (m * M) := by
  have hd : 0 < d := lt_of_lt_of_le hm h1
  have hM : 0 < M := lt_of_lt_of_le hd h2
  have key : 1 / m + 1 / M - d / (m * M) - 1 / d = (d - m) * (M - d) / (m * M * d) := by
    field_simp
    ring
  have : 0 ≤ (d - m) * (M - d) / (m * M * d) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  linarith

lemma chord2 {m M d : ℝ} (hm : 0 < m) (h1 : m ≤ d) (h2 : d ≤ M) (hmM : m < M) :
    1 / d ^ 2 ≤ ((M - d) / m ^ 2 + (d - m) / M ^ 2) / (M - m) := by
  have hd : 0 < d := lt_of_lt_of_le hm h1
  have hM : 0 < M := lt_of_lt_of_le hd h2
  have hMm : 0 < M - m := by linarith
  have key : ((M - d) / m ^ 2 + (d - m) / M ^ 2) / (M - m) - 1 / d ^ 2 =
      (d - m) * (M - d) * ((M + m) * d + m * M) / (m ^ 2 * M ^ 2 * d ^ 2) := by
    field_simp
    ring
  have : 0 ≤ (d - m) * (M - d) * ((M + m) * d + m * M) / (m ^ 2 * M ^ 2 * d ^ 2) :=
    div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity))
      (by positivity)
  linarith

/-- The three axes: `phi` is concave in `u`, so the sum is bounded below by its value at the
vertex of the simplex. -/
lemma sum_phi (s u1 u2 u3 : ℝ) (h1 : 0 ≤ u1) (h2 : 0 ≤ u2) (h3 : 0 ≤ u3)
    (hr : 0 < u1 + u2 + u3) (hm : 0 < s ^ 2 - (u1 + u2 + u3)) (hs : 1 ≤ s) :
    9 / 4 - (s ^ 2 / 4 - 1 / 16) * (1 / (s ^ 2 - (u1 + u2 + u3)) + 2 / s ^ 2)
        - (s ^ 2 * (s - 1 / 2) ^ 2 / 2) * (1 / (s ^ 2 - (u1 + u2 + u3)) ^ 2 + 2 / (s ^ 2) ^ 2)
      ≤ phi s u1 + phi s u2 + phi s u3 := by
  have hM : 0 < s ^ 2 := by positivity
  have hE : 0 ≤ s ^ 2 / 4 - 1 / 16 := by nlinarith
  have hH : 0 ≤ s ^ 2 * (s - 1 / 2) ^ 2 / 2 := by positivity
  have hmM : s ^ 2 - (u1 + u2 + u3) < s ^ 2 := by linarith
  have hm0 := hm.ne'
  have hM0 := hM.ne'
  have hr0 := hr.ne'
  have step : ∀ u : ℝ, 0 ≤ u → u ≤ u1 + u2 + u3 →
      phi s u ≥ 3 / 4 - (s ^ 2 / 4 - 1 / 16) *
          (1 / (s ^ 2 - (u1 + u2 + u3)) + 1 / s ^ 2 - (s ^ 2 - u) / ((s ^ 2 - (u1 + u2 + u3)) * s ^ 2))
        - (s ^ 2 * (s - 1 / 2) ^ 2 / 2) *
          (((s ^ 2 - (s ^ 2 - u)) / (s ^ 2 - (u1 + u2 + u3)) ^ 2 +
            ((s ^ 2 - u) - (s ^ 2 - (u1 + u2 + u3))) / (s ^ 2) ^ 2) /
            (s ^ 2 - (s ^ 2 - (u1 + u2 + u3)))) := by
    intro u hu hur
    have c1 := chord1 (m := s ^ 2 - (u1 + u2 + u3)) (M := s ^ 2) (d := s ^ 2 - u) hm
      (by linarith) (by linarith)
    have c2 := chord2 (m := s ^ 2 - (u1 + u2 + u3)) (M := s ^ 2) (d := s ^ 2 - u) hm
      (by linarith) (by linarith) hmM
    have a1 := mul_le_mul_of_nonneg_left c1 hE
    have a2 := mul_le_mul_of_nonneg_left c2 hH
    have e1 : (s ^ 2 / 4 - 1 / 16) / (s ^ 2 - u) = (s ^ 2 / 4 - 1 / 16) * (1 / (s ^ 2 - u)) := by
      ring
    have e2 : (s ^ 2 * (s - 1 / 2) ^ 2 / 2) / (s ^ 2 - u) ^ 2 =
        (s ^ 2 * (s - 1 / 2) ^ 2 / 2) * (1 / (s ^ 2 - u) ^ 2) := by ring
    unfold phi
    rw [e1, e2]
    linarith
  have s1 := step u1 h1 (by linarith)
  have s2 := step u2 h2 (by linarith)
  have s3 := step u3 h3 (by linarith)
  have hc1 : (1 / (s ^ 2 - (u1 + u2 + u3)) + 1 / s ^ 2 - (s ^ 2 - u1) / ((s ^ 2 - (u1 + u2 + u3)) * s ^ 2))
      + (1 / (s ^ 2 - (u1 + u2 + u3)) + 1 / s ^ 2 - (s ^ 2 - u2) / ((s ^ 2 - (u1 + u2 + u3)) * s ^ 2))
      + (1 / (s ^ 2 - (u1 + u2 + u3)) + 1 / s ^ 2 - (s ^ 2 - u3) / ((s ^ 2 - (u1 + u2 + u3)) * s ^ 2))
      = 1 / (s ^ 2 - (u1 + u2 + u3)) + 2 / s ^ 2 := by
    field_simp
    ring
  have hc2 : ((s ^ 2 - (s ^ 2 - u1)) / (s ^ 2 - (u1 + u2 + u3)) ^ 2 +
            ((s ^ 2 - u1) - (s ^ 2 - (u1 + u2 + u3))) / (s ^ 2) ^ 2) /
            (s ^ 2 - (s ^ 2 - (u1 + u2 + u3)))
      + ((s ^ 2 - (s ^ 2 - u2)) / (s ^ 2 - (u1 + u2 + u3)) ^ 2 +
            ((s ^ 2 - u2) - (s ^ 2 - (u1 + u2 + u3))) / (s ^ 2) ^ 2) /
            (s ^ 2 - (s ^ 2 - (u1 + u2 + u3)))
      + ((s ^ 2 - (s ^ 2 - u3)) / (s ^ 2 - (u1 + u2 + u3)) ^ 2 +
            ((s ^ 2 - u3) - (s ^ 2 - (u1 + u2 + u3))) / (s ^ 2) ^ 2) /
            (s ^ 2 - (s ^ 2 - (u1 + u2 + u3)))
      = 1 / (s ^ 2 - (u1 + u2 + u3)) ^ 2 + 2 / (s ^ 2) ^ 2 := by
    have : s ^ 2 - (s ^ 2 - (u1 + u2 + u3)) = u1 + u2 + u3 := by ring
    rw [this]
    field_simp
    ring
  have mE := congrArg (fun z => (s ^ 2 / 4 - 1 / 16) * z) hc1
  have mH := congrArg (fun z => (s ^ 2 * (s - 1 / 2) ^ 2 / 2) * z) hc2
  linarith [s1, s2, s3, mE, mH]

/-- Clearing the denominators with `m` and `M` as atoms. -/
lemma clear_den (E H m M r : ℝ) (hm : m ≠ 0) (hM : M ≠ 0) :
    (9 / 4 - E * (1 / m + 2 / M) - H * (1 / m ^ 2 + 2 / M ^ 2)) * (r * m ^ 2 * M ^ 2) =
      r * (9 / 4 * m ^ 2 * M ^ 2 - E * (m * M ^ 2 + 2 * m ^ 2 * M) - H * (M ^ 2 + 2 * m ^ 2)) := by
  field_simp

/-- The final one-variable inequality: `λ = 1/4` exactly. -/
lemma one_var (r s : ℝ) (hr : 1 ≤ r) (hs : s = r + 5 / 4) :
    (1 / 4 : ℝ) / r ≤ 9 / 4 - (s ^ 2 / 4 - 1 / 16) * (1 / (s ^ 2 - r) + 2 / s ^ 2)
        - (s ^ 2 * (s - 1 / 2) ^ 2 / 2) * (1 / (s ^ 2 - r) ^ 2 + 2 / (s ^ 2) ^ 2) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ r = 1 + t := ⟨r - 1, by linarith, by ring⟩
  subst hs
  have h0 : 0 < 1 + t := by linarith
  have h1 : 0 < (1 + t + 5 / 4) ^ 2 - (1 + t) := by nlinarith
  have h2 : 0 < (1 + t + 5 / 4) ^ 2 := by positivity
  have hD : 0 < (1 + t) * ((1 + t + 5 / 4) ^ 2 - (1 + t)) ^ 2 * ((1 + t + 5 / 4) ^ 2) ^ 2 := by
    positivity
  have e := clear_den ((1 + t + 5 / 4) ^ 2 / 4 - 1 / 16)
    ((1 + t + 5 / 4) ^ 2 * (1 + t + 5 / 4 - 1 / 2) ^ 2 / 2)
    ((1 + t + 5 / 4) ^ 2 - (1 + t)) ((1 + t + 5 / 4) ^ 2) (1 + t) h1.ne' h2.ne'
  refine le_of_mul_le_mul_right ?_ hD
  rw [e]
  have key : (1 / 4 : ℝ) / (1 + t) *
      ((1 + t) * ((1 + t + 5 / 4) ^ 2 - (1 + t)) ^ 2 * ((1 + t + 5 / 4) ^ 2) ^ 2) =
      1 / 4 * ((1 + t + 5 / 4) ^ 2 - (1 + t)) ^ 2 * ((1 + t + 5 / 4) ^ 2) ^ 2 := by
    have := h0.ne'
    field_simp
  rw [key, ← sub_nonneg]
  have poly : (1 + t) * (9 / 4 * ((1 + t + 5 / 4) ^ 2 - (1 + t)) ^ 2 * ((1 + t + 5 / 4) ^ 2) ^ 2
        - ((1 + t + 5 / 4) ^ 2 / 4 - 1 / 16) *
          (((1 + t + 5 / 4) ^ 2 - (1 + t)) * ((1 + t + 5 / 4) ^ 2) ^ 2
            + 2 * ((1 + t + 5 / 4) ^ 2 - (1 + t)) ^ 2 * (1 + t + 5 / 4) ^ 2)
        - ((1 + t + 5 / 4) ^ 2 * (1 + t + 5 / 4 - 1 / 2) ^ 2 / 2) *
          (((1 + t + 5 / 4) ^ 2) ^ 2 + 2 * ((1 + t + 5 / 4) ^ 2 - (1 + t)) ^ 2))
      - 1 / 4 * ((1 + t + 5 / 4) ^ 2 - (1 + t)) ^ 2 * ((1 + t + 5 / 4) ^ 2) ^ 2 =
      17064027 / 262144 + t * (16640955 / 65536) + t ^ 2 * (6421495 / 16384) +
        t ^ 3 * (1309135 / 4096) + t ^ 4 * (153665 / 1024) + t ^ 5 * (10353 / 256) +
        t ^ 6 * (365 / 64) + t ^ 7 * (5 / 16) := by
    ring
  rw [poly]
  positivity


/-! ## The cube on integer sites -/

/-- Integer coordinates of a site. -/
def xi (p : ℤ × ℤ × ℤ) : Fin 3 → ℝ
  | 0 => (p.1 : ℝ)
  | 1 => (p.2.1 : ℝ)
  | 2 => (p.2.2 : ℝ)

/-- The squared distance, in steps, from the nucleus cell. -/
def RN (p : ℤ × ℤ × ℤ) : ℝ := ∑ j, xi p j ^ 2

lemma RN_eq (p : ℤ × ℤ × ℤ) : RN p = xi p 0 ^ 2 + xi p 1 ^ 2 + xi p 2 ^ 2 := by
  simp [RN, Fin.sum_univ_three]

lemma xi_sub (p : ℤ × ℤ × ℤ) (i j : Fin 3) :
    xi (p - axis i) j = if j = i then xi p j - 1 else xi p j := by
  fin_cases i <;> fin_cases j <;> simp [xi, axis]

lemma RN_rest_sub (p : ℤ × ℤ × ℤ) (i : Fin 3) :
    RN (p - axis i) - xi (p - axis i) i ^ 2 = RN p - xi p i ^ 2 := by
  unfold RN
  simp only [Fin.sum_univ_three, xi_sub]
  fin_cases i <;> simp <;> ring

lemma rest_nonneg (p : ℤ × ℤ × ℤ) (i : Fin 3) : 0 ≤ RN p - xi p i ^ 2 := by
  rw [RN_eq]
  fin_cases i <;> simp <;>
    nlinarith [sq_nonneg (xi p 0), sq_nonneg (xi p 1), sq_nonneg (xi p 2)]

lemma RN_ge_one (p : ℤ × ℤ × ℤ) (hp : p ≠ 0) : 1 ≤ RN p := by
  obtain ⟨a, b, c⟩ := p
  have hint : (1 : ℤ) ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
    by_contra h
    push Not at h
    have ha : a = 0 := by
      have h1 : a ^ 2 ≤ 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
      exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h1 (sq_nonneg a))
    have hb : b = 0 := by
      have h1 : b ^ 2 ≤ 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
      exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h1 (sq_nonneg b))
    have hc : c = 0 := by
      have h1 : c ^ 2 ≤ 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
      exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h1 (sq_nonneg c))
    exact hp (by simp [ha, hb, hc])
  rw [RN_eq]
  simp only [xi]
  exact_mod_cast hint

/-- The field on the edge `p → p + e_i`. -/
def kapN (i : Fin 3) (p : ℤ × ℤ × ℤ) : ℝ := kk (xi p i + 1 / 2) (RN p - xi p i ^ 2)

lemma kapN_sub (i : Fin 3) (p : ℤ × ℤ × ℤ) :
    kapN i (p - axis i) = kk (xi p i - 1 / 2) (RN p - xi p i ^ 2) := by
  unfold kapN
  rw [RN_rest_sub, xi_sub]
  simp only [↓reduceIte]
  have : xi p i - 1 + 1 / 2 = xi p i - 1 / 2 := by ring
  rw [this]

lemma wN_eq (p : ℤ × ℤ × ℤ) :
    wVF kapN p = ∑ i : Fin 3, fax (xi p i) (RN p - xi p i ^ 2) := by
  unfold wVF
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kapN_sub]
  rfl

/-- **The weight of the field is at least `1/(4 r²)` away from the nucleus.** -/
lemma weight_ge (p : ℤ × ℤ × ℤ) (hp : p ≠ 0) : (1 / 4) * (1 / RN p) ≤ wVF kapN p := by
  rw [wN_eq]
  have hr := RN_ge_one p hp
  have hq := rest_nonneg p
  have e : ∀ i, fax (xi p i) (RN p - xi p i ^ 2) = phi (RN p + 5 / 4) (xi p i ^ 2) := by
    intro i
    rw [fax_eq _ _ (hq i)]
    congr 1
    ring
  simp only [e, Fin.sum_univ_three]
  have hsum : xi p 0 ^ 2 + xi p 1 ^ 2 + xi p 2 ^ 2 = RN p := (RN_eq p).symm
  have hm : 0 < (RN p + 5 / 4) ^ 2 - (xi p 0 ^ 2 + xi p 1 ^ 2 + xi p 2 ^ 2) := by
    rw [hsum]; nlinarith
  have h := sum_phi (RN p + 5 / 4) (xi p 0 ^ 2) (xi p 1 ^ 2) (xi p 2 ^ 2) (sq_nonneg _)
    (sq_nonneg _) (sq_nonneg _) (by rw [hsum]; linarith) hm (by linarith)
  rw [hsum] at h
  have h1 := one_var (RN p) (RN p + 5 / 4) hr rfl
  calc (1 / 4) * (1 / RN p) = (1 / 4) / RN p := by ring
    _ ≤ _ := h1
    _ ≤ _ := h

/-- **Hardy's inequality on the integer sites, with the constant `1/4`**, for every finite
support. -/
theorem hardy_entero (S : Finset (ℤ × ℤ × ℤ)) (ψ : ℤ × ℤ × ℤ → ℝ) (hψ : ∀ p ∉ S, ψ p = 0)
    (h0 : ψ 0 = 0) :
    (1 / 4) * ∑ p ∈ S, (1 / RN p) * ψ p ^ 2 ≤
      ∑ i : Fin 3, ∑ p ∈ edgeBase S i, (ψ (p + axis i) - ψ p) ^ 2 := by
  refine le_trans ?_ (hardy_vf S kapN ψ hψ)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases hp : p = 0
  · subst hp
    simp [h0]
  · rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (weight_ge p hp) (sq_nonneg _)

end

end NRS3Hidrogeno

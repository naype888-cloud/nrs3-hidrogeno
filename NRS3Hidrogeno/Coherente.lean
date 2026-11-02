import Mathlib
import NRS3Hidrogeno.Espin

/-!
# The coherent states of `d = 3` saturate, and they are the Bloch sphere

A qubit `(a, b)` of unit norm has the symmetric square `ψ = (a², √2 a b, b²)`, a state of the three
positions. For the pair `(T, Z) = (T3, Z3)` of `Espin` (`T3` the hop, `Z3 = P - 1`):

* the centred vectors `(T - ⟨T⟩) ψ` and `(Z - ⟨Z⟩) ψ` are both multiples of one vector `χ`
  (`cen_T`, `cen_Z`): `(a² - b²) χ` and `√2 a b χ`;
* so the Gram defect, the Cauchy–Schwarz gap of the two centred vectors, is `0`
  (`coherent_saturates`): the coherent states saturate the Robertson–Schrödinger relation at
  `d = 3`, as the pure states do at `d = 2`;
* the expectations are `⟨T⟩ = √2 · 2 Re(ā b)` and `⟨Z⟩ = |b|² - |a|²` (`mean_T`, `mean_Z`): the
  vector `(2 Re(ā b), 2 Im(ā b), |b|² - |a|²)` is a point of the unit sphere (`sphere`), the Bloch
  vector of the qubit `(a, b)`.

So the saturating coherent states of `d = 3` form the sphere of `d = 2`. They are not all the
saturating states: `D23` (`gramDefectAt_eq_zero_iff`) classifies them all.
-/

namespace NRS3Hidrogeno

open Matrix ComplexConjugate

noncomputable section

/-- `√2` as a complex number. -/
def s2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

lemma s2_sq : s2 * s2 = 2 := by
  unfold s2
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  simp

lemma conj_s2 : conj s2 = s2 := by
  unfold s2
  exact Complex.conj_ofReal _

/-- The coherent state: the symmetric square of the qubit `(a, b)`. -/
def coh (a b : ℂ) : Fin 3 → ℂ := ![a ^ 2, s2 * a * b, b ^ 2]

/-- The vector in which both centred vectors lie. -/
def chi (a b : ℂ) : Fin 3 → ℂ := ![-s2 * a * conj b, a * conj a - b * conj b, s2 * conj a * b]

/-- The expectation. -/
def mean3 (M : Matrix (Fin 3) (Fin 3) ℂ) (ψ : Fin 3 → ℂ) : ℂ :=
  ∑ i, conj (ψ i) * (M.mulVec ψ) i

/-- The centred vector `(M - ⟨M⟩) ψ`. -/
def cen3 (M : Matrix (Fin 3) (Fin 3) ℂ) (ψ : Fin 3 → ℂ) : Fin 3 → ℂ :=
  M.mulVec ψ - mean3 M ψ • ψ

/-- The squared norm. -/
def nsq (u : Fin 3 → ℂ) : ℝ := ∑ i, Complex.normSq (u i)

/-- The inner product. -/
def inn (u v : Fin 3 → ℂ) : ℂ := ∑ i, conj (u i) * v i

/-- The Gram defect: the Cauchy–Schwarz gap `‖u‖² ‖v‖² - |⟨u, v⟩|²`. -/
def gram3 (u v : Fin 3 → ℂ) : ℝ := nsq u * nsq v - Complex.normSq (inn u v)

lemma gram3_smul (α β : ℂ) (χ : Fin 3 → ℂ) : gram3 (α • χ) (β • χ) = 0 := by
  have h1 : nsq (α • χ) = Complex.normSq α * nsq χ := by
    unfold nsq
    simp [Complex.normSq_mul, Finset.mul_sum]
  have h2 : nsq (β • χ) = Complex.normSq β * nsq χ := by
    unfold nsq
    simp [Complex.normSq_mul, Finset.mul_sum]
  have h3 : inn (α • χ) (β • χ) = conj α * β * (nsq χ : ℂ) := by
    unfold inn nsq
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  unfold gram3
  rw [h1, h2, h3, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_conj,
    Complex.normSq_ofReal]
  ring

variable {a b : ℂ}

/-- The unit norm of the qubit, `|a|² + |b|² = 1`, in complex form. -/
lemma mean_T (h : a * conj a + b * conj b = 1) :
    mean3 T3 (coh a b) = s2 * (conj a * b + a * conj b) := by
  unfold mean3 coh T3
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, conj_s2]
  linear_combination (s2 * (conj a * b + a * conj b)) * h

lemma mean_Z (h : a * conj a + b * conj b = 1) :
    mean3 Z3 (coh a b) = b * conj b - a * conj a := by
  unfold mean3 coh Z3
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  linear_combination (b * conj b - a * conj a) * h

lemma cen_Z (h : a * conj a + b * conj b = 1) :
    cen3 Z3 (coh a b) = (s2 * a * b) • chi a b := by
  unfold cen3
  rw [mean_Z h]
  ext i
  fin_cases i
  · simp [coh, chi, Z3]
    linear_combination a ^ 2 * h + (a ^ 2 * b * conj b) * s2_sq
  · simp [coh, chi, Z3]
    ring
  · simp [coh, chi, Z3]
    linear_combination (-b ^ 2) * h + (-(b ^ 2) * (a * conj a)) * s2_sq

lemma cen_T (h : a * conj a + b * conj b = 1) :
    cen3 T3 (coh a b) = (a ^ 2 - b ^ 2) • chi a b := by
  unfold cen3
  rw [mean_T h]
  ext i
  fin_cases i
  · simp [coh, chi, T3]
    linear_combination (-(s2 * a * b)) * h
  · simp [coh, chi, T3]
    linear_combination (-(a ^ 2 + b ^ 2)) * h +
      (-((a * conj a) * b ^ 2 + a ^ 2 * (b * conj b))) * s2_sq
  · simp [coh, chi, T3]
    linear_combination (-(s2 * a * b)) * h

/-- **The coherent states of `d = 3` saturate**: the Gram defect of the centred vectors of the hop
and of the position is zero. -/
theorem coherent_saturates (h : a * conj a + b * conj b = 1) :
    gram3 (cen3 T3 (coh a b)) (cen3 Z3 (coh a b)) = 0 := by
  rw [cen_T h, cen_Z h]
  exact gram3_smul _ _ _

/-- **The expectation of the hop is `√2` times the first Bloch coordinate `2 Re(ā b)`.** -/
lemma mean_T_re (h : a * conj a + b * conj b = 1) :
    mean3 T3 (coh a b) = s2 * ((2 * (conj a * b).re : ℝ) : ℂ) := by
  rw [mean_T h]
  congr 1
  have := Complex.add_conj (conj a * b)
  simpa [map_mul, Complex.conj_conj] using this

/-- **The expectation of the position is the third Bloch coordinate `|b|² - |a|²`.** -/
lemma mean_Z_re (h : a * conj a + b * conj b = 1) :
    mean3 Z3 (coh a b) = ((Complex.normSq b - Complex.normSq a : ℝ) : ℂ) := by
  rw [mean_Z h, Complex.mul_conj, Complex.mul_conj]
  push_cast
  ring

/-- **The Bloch vector of the qubit `(a, b)` lies on the unit sphere.** -/
lemma sphere (hn : Complex.normSq a + Complex.normSq b = 1) :
    (2 * (conj a * b).re) ^ 2 + (2 * (conj a * b).im) ^ 2 +
      (Complex.normSq b - Complex.normSq a) ^ 2 = 1 := by
  have h1 : (conj a * b).re ^ 2 + (conj a * b).im ^ 2 =
      Complex.normSq a * Complex.normSq b := by
    have := Complex.normSq_apply (conj a * b)
    rw [Complex.normSq_mul, Complex.normSq_conj] at this
    nlinarith [this]
  calc (2 * (conj a * b).re) ^ 2 + (2 * (conj a * b).im) ^ 2 +
        (Complex.normSq b - Complex.normSq a) ^ 2
      = 4 * ((conj a * b).re ^ 2 + (conj a * b).im ^ 2) +
        (Complex.normSq b - Complex.normSq a) ^ 2 := by ring
    _ = 4 * (Complex.normSq a * Complex.normSq b) +
        (Complex.normSq b - Complex.normSq a) ^ 2 := by rw [h1]
    _ = (Complex.normSq a + Complex.normSq b) ^ 2 := by ring
    _ = 1 := by rw [hn]; norm_num

end

end NRS3Hidrogeno

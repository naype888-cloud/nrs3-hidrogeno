import Mathlib

/-!
# The commutators of the pair `(T_d, P_d)` close exactly for `d = 2, 3`

`T_d` is the hop of the path of `d` positions, `T = S + Sᵀ` with `S` the shift, and `P_d` the
position, the diagonal `0, 1, …, d - 1`. Then `[T, P] = Sᵀ - S` and
`[T, [T, P]] = 2 [S, Sᵀ] = diag(-2, 0, …, 0, 2)`: an operator of the border, equal to
`2 (P - 1)` for `d = 3` and to `4 P - 2` for `d = 2`, and not a combination of `P` and `1` from
`d = 4` on (`closes_iff`). Together with `[T, P] = Sᵀ - S` and `[P, [T, P]] = -T`
(`br_Pp_br_Tp_Pp`, true for every `d`), the span of `{T, P, [T, P], 1}` is closed under the
commutator exactly for `d ≤ 3`: three generators with the relations of an angular momentum. The
reading is spin `1/2` for `d = 2`, the `σₓ, σ_z` of `BolaDeBloch`, and spin `1` for `d = 3`; that
identification is not proved here. From `d = 4` the commutators of `T` and `P` do not close, and
that is where the Robertson–Schrödinger inequality is strict (`D22`, `D39`).

The hop of the corpus is `A_d = ρ_d T_d` (`D3`); the scale `ρ_d` does not change what closes.
-/

namespace NRS3Hidrogeno

open Matrix

noncomputable section

variable (d : ℕ)

/-- The shift of the path: `S e_j = e_{j+1}`. -/
def Sh : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => if i.val = j.val + 1 then 1 else 0

/-- The hop of the path of `d` positions. -/
def Tp : Matrix (Fin d) (Fin d) ℝ := Sh d + (Sh d)ᵀ

/-- The position: the values `0, 1, …, d - 1`. -/
def Pp : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal fun i => (i.val : ℝ)

/-- The commutator. -/
def br {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ) : Matrix n n ℝ :=
  A * B - B * A

open Classical in
/-- The hop is the adjacency matrix of the path graph. -/
lemma Tp_eq_adj : Tp d = (SimpleGraph.pathGraph d).adjMatrix ℝ := by
  ext i j
  simp only [Tp, Sh, Matrix.add_apply, Matrix.of_apply, Matrix.transpose_apply,
    SimpleGraph.adjMatrix_apply, SimpleGraph.pathGraph_adj]
  split_ifs <;> first | omega | norm_num

lemma br_Sh_Pp : br (Sh d) (Pp d) = -Sh d := by
  ext i j
  simp only [br, Pp, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply,
    Sh, Matrix.of_apply]
  by_cases h : i.val = j.val + 1
  · have : (i.val : ℝ) = j.val + 1 := by exact_mod_cast h
    simp [h]
  · simp [h]

lemma br_ShT_Pp : br (Sh d)ᵀ (Pp d) = (Sh d)ᵀ := by
  ext i j
  simp only [br, Pp, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.transpose_apply, Sh, Matrix.of_apply]
  by_cases h : j.val = i.val + 1
  · have : (j.val : ℝ) = i.val + 1 := by exact_mod_cast h
    simp [h]
  · simp [h]

/-- `[T, P] = Sᵀ - S`. -/
lemma br_Tp_Pp : br (Tp d) (Pp d) = (Sh d)ᵀ - Sh d := by
  have h1 := br_Sh_Pp d
  have h2 := br_ShT_Pp d
  unfold br at h1 h2 ⊢
  unfold Tp
  rw [add_mul, mul_add]
  calc _ = (Sh d * Pp d - Pp d * Sh d) + ((Sh d)ᵀ * Pp d - Pp d * (Sh d)ᵀ) := by abel
    _ = _ := by rw [h1, h2]; abel

/-- `[P, [T, P]] = -T`: this one closes for every `d`. -/
lemma br_Pp_br_Tp_Pp : br (Pp d) (br (Tp d) (Pp d)) = -Tp d := by
  have h1 := br_Sh_Pp d
  have h2 := br_ShT_Pp d
  rw [br_Tp_Pp]
  unfold br at h1 h2 ⊢
  unfold Tp
  calc Pp d * ((Sh d)ᵀ - Sh d) - ((Sh d)ᵀ - Sh d) * Pp d
      = -((Sh d)ᵀ * Pp d - Pp d * (Sh d)ᵀ) + (Sh d * Pp d - Pp d * Sh d) := by
        simp only [mul_sub, sub_mul]
        abel
    _ = -(Sh d + (Sh d)ᵀ) := by rw [h1, h2]; abel

/-- `S Sᵀ` is the projector on the positions `≥ 1`. -/
lemma Sh_mul_ShT : Sh d * (Sh d)ᵀ = Matrix.diagonal fun i => if 1 ≤ i.val then (1 : ℝ) else 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Sh, Matrix.of_apply, Matrix.diagonal_apply,
    Fin.ext_iff]
  by_cases hi : 1 ≤ i.val
  · rw [Finset.sum_eq_single (⟨i.val - 1, by omega⟩ : Fin d)]
    · dsimp only
      split_ifs <;> first | (norm_num; done) | (exfalso; omega)
    · intro k _ hk
      have : ¬ i.val = k.val + 1 := fun h => hk (Fin.ext (by simp; omega))
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine (Finset.sum_eq_zero fun k _ => ?_).trans ?_
    · have : ¬ i.val = k.val + 1 := by omega
      simp [this]
    · simp [hi]

/-- `Sᵀ S` is the projector on the positions `< d - 1`. -/
lemma ShT_mul_Sh : (Sh d)ᵀ * Sh d =
    Matrix.diagonal fun i => if i.val + 1 < d then (1 : ℝ) else 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Sh, Matrix.of_apply, Matrix.diagonal_apply,
    Fin.ext_iff]
  by_cases hi : i.val + 1 < d
  · rw [Finset.sum_eq_single (⟨i.val + 1, hi⟩ : Fin d)]
    · dsimp only
      split_ifs <;> first | (norm_num; done) | (exfalso; omega)
    · intro k _ hk
      have : ¬ k.val = i.val + 1 := fun h => hk (Fin.ext (by simp; omega))
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine (Finset.sum_eq_zero fun k _ => ?_).trans ?_
    · have : ¬ k.val = i.val + 1 := by omega
      simp [this]
    · simp [hi]

/-- The double commutator `[T, [T, P]]`. -/
def dbl : Matrix (Fin d) (Fin d) ℝ := br (Tp d) (br (Tp d) (Pp d))

/-- **`[T, [T, P]]` is the operator of the border `diag(-2, 0, …, 0, 2)`.** -/
theorem dbl_eq : dbl d = Matrix.diagonal fun i =>
    2 * ((if 1 ≤ i.val then (1 : ℝ) else 0) - (if i.val + 1 < d then 1 else 0)) := by
  unfold dbl
  rw [br_Tp_Pp]
  have h : br (Tp d) ((Sh d)ᵀ - Sh d) = (2 : ℝ) • (Sh d * (Sh d)ᵀ - (Sh d)ᵀ * Sh d) := by
    unfold br Tp
    simp only [add_mul, mul_add, sub_mul, mul_sub, two_smul]
    abel
  rw [h, Sh_mul_ShT, ShT_mul_Sh]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- **The pair `(T_d, P_d)` closes — `[T, [T, P]]` is a combination of `P` and `1` — exactly when
`d ≤ 3`**: `su(2)` (the Bloch sphere for `d = 2`, spin one for `d = 3`); from `d = 4` it does
not. -/
theorem closes_iff :
    (∃ a b : ℝ, dbl d = a • Pp d + b • (1 : Matrix (Fin d) (Fin d) ℝ)) ↔ d ≤ 3 := by
  constructor
  · rintro ⟨a, b, h⟩
    by_contra hd
    push Not at hd
    have hd' : ∀ i : Fin d, 2 * ((if 1 ≤ i.val then (1 : ℝ) else 0) -
        (if i.val + 1 < d then 1 else 0)) = a * i.val + b := by
      intro i
      have := congrFun (congrFun h i) i
      rw [dbl_eq] at this
      simpa [Pp, Matrix.diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply_eq] using this
    have e0 := hd' ⟨0, by omega⟩
    have e1 := hd' ⟨1, by omega⟩
    have e2 := hd' ⟨2, by omega⟩
    norm_num [show (0 : ℕ) + 1 < d by omega, show (1 : ℕ) + 1 < d by omega,
      show (2 : ℕ) + 1 < d by omega] at e0 e1 e2
    linarith
  · intro hd
    interval_cases d
    · exact ⟨0, 0, by ext i; exact Fin.elim0 i⟩
    · exact ⟨0, 0, by ext i j; fin_cases i; fin_cases j; simp [dbl_eq, Pp]⟩
    · refine ⟨4, -2, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [dbl_eq, Pp]
      all_goals norm_num
    · refine ⟨2, -2, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [dbl_eq, Pp]
      all_goals norm_num

end

end NRS3Hidrogeno

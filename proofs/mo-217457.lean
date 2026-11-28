import OMAStatements.S_mo_217457

/-!
# The determinants of the three-seasonal risk model (MathOverflow 217457)

The statement asks, for every joint law of three claims with `0 < s 0 < 1`, whether the determinants
`D n = α n * β (n + 1) - β n * α (n + 1)` are positive and strictly increasing (and whether the determinants
with the rows `n` and `n + 2` are negative and strictly decreasing).

* `OMA.disproof`: this fails already for independent claims. If the first claim is a fair coin and the
  other two claims vanish, then `D 1 = D 0 = 1`.
* `OMA.core`: what is true for independent claims, in full generality. If `a`, `b`, `c` are the local
  probabilities of three independent claims (nonnegative, partial sums at most one, positive at zero), `s` is
  their convolution and `α`, `β` satisfy the two recurrences of the source, then `0 < D n` and
  `D n ≤ D (n + 1)` for every `n`. So for independent claims the strict claim can only fail in the weak
  form `D (n + 1) = D n`.

Idea of the proof of `OMA.core`. With `F(z)` the matrix of the three generating functions, arranged
cyclically, the two sequences of the source are differences of the entries of the first row of the
coefficients of `(F(z) - z)⁻¹`; in terms of the walk that runs through the claims in the reverse order, these
are the values `h n` of the harmonic function that starts from `(1, 0, 0)` on level zero, and
`D n = c 0 * det (1, h (n + 1), h n)`. On the levels `≥ 2` both `h` and `h` moved up by one level are harmonic
for the same killed walk, so both are carried from level `u + 1` to level `u` by the matrix `Y u` of the
probabilities to pass from level `u` to level `u + 1`. Hence
`det (x, h (n + 2), h (n + 1)) * det (Y (n + 1)) = det (Y (n + 1) x, h (n + 1), h n)`. The matrix `Y u` has
nonnegative entries, positive determinant, and every row sum of `Y u` is at least `det (Y u)`: this is where
the probabilistic structure enters (`Y u = (1 - M u)⁻¹ F₀` for a matrix `M u` of return probabilities, whose
row sums are at most one minus the probability of an up-step). Positivity and monotonicity follow by
induction on `n`.
-/

open Finset Matrix

namespace OMA

/-- The adjugate of `1 - M` for a `3 × 3` matrix, written out. -/
lemma adj_one_sub (M : Matrix (Fin 3) (Fin 3) ℝ) :
    adjugate (1 - M) =
      !![(1 - M 1 1) * (1 - M 2 2) - M 1 2 * M 2 1, M 0 1 * (1 - M 2 2) + M 0 2 * M 2 1,
          M 0 1 * M 1 2 + M 0 2 * (1 - M 1 1);
        M 1 0 * (1 - M 2 2) + M 1 2 * M 2 0, (1 - M 0 0) * (1 - M 2 2) - M 0 2 * M 2 0,
          (1 - M 0 0) * M 1 2 + M 0 2 * M 1 0;
        M 1 0 * M 2 1 + (1 - M 1 1) * M 2 0, (1 - M 0 0) * M 2 1 + M 0 1 * M 2 0,
          (1 - M 0 0) * (1 - M 1 1) - M 0 1 * M 1 0] := by
  rw [adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply]

/-- The determinant of `1 - M`, expanded along the row sums. -/
lemma det_one_sub (M : Matrix (Fin 3) (Fin 3) ℝ) :
    det (1 - M) =
      ((1 - M 1 1) * (1 - M 2 2) - M 1 2 * M 2 1) * (1 - M 0 0 - M 0 1 - M 0 2) +
      (M 0 1 * (1 - M 2 2) + M 0 2 * M 2 1) * (1 - M 1 0 - M 1 1 - M 1 2) +
      (M 0 1 * M 1 2 + M 0 2 * (1 - M 1 1)) * (1 - M 2 0 - M 2 1 - M 2 2) := by
  rw [det_fin_three]
  simp [Matrix.sub_apply]
  ring

/-- Substochastic matrices: nonnegative entries, row sums at most `1 - φ i` with `φ i > 0`. -/
structure Sub (M : Matrix (Fin 3) (Fin 3) ℝ) (φ : Fin 3 → ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ M i j
  pos : ∀ i, 0 < φ i
  row : ∀ i, M i 0 + M i 1 + M i 2 ≤ 1 - φ i

lemma Sub.adj_nonneg {M : Matrix (Fin 3) (Fin 3) ℝ} {φ : Fin 3 → ℝ} (h : Sub M φ) (i j : Fin 3) :
    0 ≤ adjugate (1 - M) i j := by
  have h00 := h.nonneg 0 0; have h01 := h.nonneg 0 1; have h02 := h.nonneg 0 2
  have h10 := h.nonneg 1 0; have h11 := h.nonneg 1 1; have h12 := h.nonneg 1 2
  have h20 := h.nonneg 2 0; have h21 := h.nonneg 2 1; have h22 := h.nonneg 2 2
  have r0 := h.row 0; have r1 := h.row 1; have r2 := h.row 2
  have p0 := h.pos 0; have p1 := h.pos 1; have p2 := h.pos 2
  have e0 : 0 ≤ 1 - M 0 0 := by linarith
  have e1 : 0 ≤ 1 - M 1 1 := by linarith
  have e2 : 0 ≤ 1 - M 2 2 := by linarith
  rw [adj_one_sub]
  fin_cases i <;> fin_cases j <;> simp
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - M 1 1 - M 1 2) (by linarith : (0:ℝ) ≤ 1 - M 2 2 - M 2 1),
      mul_nonneg h12 (by linarith : (0:ℝ) ≤ 1 - M 2 2 - M 2 1),
      mul_nonneg h21 (by linarith : (0:ℝ) ≤ 1 - M 1 1 - M 1 2)]
  · positivity
  · positivity
  · positivity
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - M 0 0 - M 0 2) (by linarith : (0:ℝ) ≤ 1 - M 2 2 - M 2 0),
      mul_nonneg h02 (by linarith : (0:ℝ) ≤ 1 - M 2 2 - M 2 0),
      mul_nonneg h20 (by linarith : (0:ℝ) ≤ 1 - M 0 0 - M 0 2)]
  · positivity
  · positivity
  · positivity
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - M 0 0 - M 0 1) (by linarith : (0:ℝ) ≤ 1 - M 1 1 - M 1 0),
      mul_nonneg h01 (by linarith : (0:ℝ) ≤ 1 - M 1 1 - M 1 0),
      mul_nonneg h10 (by linarith : (0:ℝ) ≤ 1 - M 0 0 - M 0 1)]

/-- the diagonal entries of the adjugate dominate the product of the other two `φ`s -/
lemma Sub.adj_diag {M : Matrix (Fin 3) (Fin 3) ℝ} {φ : Fin 3 → ℝ} (h : Sub M φ) :
    φ 1 * φ 2 ≤ adjugate (1 - M) 0 0 ∧ φ 0 * φ 2 ≤ adjugate (1 - M) 1 1 ∧
      φ 0 * φ 1 ≤ adjugate (1 - M) 2 2 := by
  have h00 := h.nonneg 0 0; have h01 := h.nonneg 0 1; have h02 := h.nonneg 0 2
  have h10 := h.nonneg 1 0; have h11 := h.nonneg 1 1; have h12 := h.nonneg 1 2
  have h20 := h.nonneg 2 0; have h21 := h.nonneg 2 1; have h22 := h.nonneg 2 2
  have r0 := h.row 0; have r1 := h.row 1; have r2 := h.row 2
  have p0 := h.pos 0; have p1 := h.pos 1; have p2 := h.pos 2
  rw [adj_one_sub]
  simp
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_le_mul (by linarith : φ 1 ≤ 1 - M 1 1 - M 1 2) (by linarith : φ 2 ≤ 1 - M 2 2 - M 2 1) p2.le
        (by linarith : (0:ℝ) ≤ 1 - M 1 1 - M 1 2),
      mul_nonneg h12 (by linarith : (0:ℝ) ≤ 1 - M 2 2 - M 2 1),
      mul_nonneg h21 (by linarith : (0:ℝ) ≤ 1 - M 1 1 - M 1 2)]
  · nlinarith [mul_le_mul (by linarith : φ 0 ≤ 1 - M 0 0 - M 0 2) (by linarith : φ 2 ≤ 1 - M 2 2 - M 2 0) p2.le
        (by linarith : (0:ℝ) ≤ 1 - M 0 0 - M 0 2),
      mul_nonneg h02 (by linarith : (0:ℝ) ≤ 1 - M 2 2 - M 2 0),
      mul_nonneg h20 (by linarith : (0:ℝ) ≤ 1 - M 0 0 - M 0 2)]
  · nlinarith [mul_le_mul (by linarith : φ 0 ≤ 1 - M 0 0 - M 0 1) (by linarith : φ 1 ≤ 1 - M 1 1 - M 1 0) p1.le
        (by linarith : (0:ℝ) ≤ 1 - M 0 0 - M 0 1),
      mul_nonneg h01 (by linarith : (0:ℝ) ≤ 1 - M 1 1 - M 1 0),
      mul_nonneg h10 (by linarith : (0:ℝ) ≤ 1 - M 0 0 - M 0 1)]

/-- the determinant of `1 - M` is at least the product of the `φ`s -/
lemma Sub.det_ge {M : Matrix (Fin 3) (Fin 3) ℝ} {φ : Fin 3 → ℝ} (h : Sub M φ) :
    φ 0 * φ 1 * φ 2 ≤ det (1 - M) := by
  have h00 := h.nonneg 0 0; have h01 := h.nonneg 0 1; have h02 := h.nonneg 0 2
  have h10 := h.nonneg 1 0; have h11 := h.nonneg 1 1; have h12 := h.nonneg 1 2
  have h20 := h.nonneg 2 0; have h21 := h.nonneg 2 1; have h22 := h.nonneg 2 2
  have r0 := h.row 0; have r1 := h.row 1; have r2 := h.row 2
  have p0 := h.pos 0; have p1 := h.pos 1; have p2 := h.pos 2
  have hd := h.adj_diag.1
  have ha1 := h.adj_nonneg 0 1
  have ha2 := h.adj_nonneg 0 2
  rw [adj_one_sub] at hd ha1 ha2
  simp at hd ha1 ha2
  rw [det_one_sub]
  have t1 : φ 1 * φ 2 * φ 0 ≤ ((1 - M 1 1) * (1 - M 2 2) - M 1 2 * M 2 1) * (1 - M 0 0 - M 0 1 - M 0 2) :=
    mul_le_mul hd (by linarith) p0.le (le_trans (by positivity) hd)
  have t2 : 0 ≤ (M 0 1 * (1 - M 2 2) + M 0 2 * M 2 1) * (1 - M 1 0 - M 1 1 - M 1 2) :=
    mul_nonneg ha1 (by linarith)
  have t3 : 0 ≤ (M 0 1 * M 1 2 + M 0 2 * (1 - M 1 1)) * (1 - M 2 0 - M 2 1 - M 2 2) :=
    mul_nonneg ha2 (by linarith)
  nlinarith

lemma Sub.det_pos {M : Matrix (Fin 3) (Fin 3) ℝ} {φ : Fin 3 → ℝ} (h : Sub M φ) : 0 < det (1 - M) :=
  lt_of_lt_of_le (mul_pos (mul_pos (h.pos 0) (h.pos 1)) (h.pos 2)) h.det_ge



variable (a b c : ℕ → ℝ)

/-- step matrices of the reversed walk: from phase `0` to phase `2` with `c`, from `1` to `0` with `a`,
from `2` to `1` with `b` -/
def Ft (k : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, c k; a k, 0, 0; 0, b k, 0]

/-- the probabilities of an up-step, by phase of the reversed walk -/
def phi : Fin 3 → ℝ := ![c 0, a 0, b 0]

/-- passage matrix one level up, from the return matrix `M` -/
noncomputable def Yof (M : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (det (1 - M))⁻¹ • (adjugate (1 - M) * Ft a b c 0)

lemma mulVec_mono {N : Matrix (Fin 3) (Fin 3) ℝ} (hN : ∀ i j, 0 ≤ N i j) {x y : Fin 3 → ℝ}
    (hxy : ∀ i, x i ≤ y i) (i : Fin 3) : (N *ᵥ x) i ≤ (N *ᵥ y) i := by
  simp only [mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hxy j) (hN i j)

lemma mulVec_nonneg {N : Matrix (Fin 3) (Fin 3) ℝ} (hN : ∀ i j, 0 ≤ N i j) {x : Fin 3 → ℝ}
    (hx : ∀ i, 0 ≤ x i) (i : Fin 3) : 0 ≤ (N *ᵥ x) i := by
  simp only [mulVec, dotProduct]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hN i j) (hx j)

lemma mul_nonneg_entries {N N' : Matrix (Fin 3) (Fin 3) ℝ} (hN : ∀ i j, 0 ≤ N i j)
    (hN' : ∀ i j, 0 ≤ N' i j) (i j : Fin 3) : 0 ≤ (N * N') i j := by
  simp only [Matrix.mul_apply]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hN i k) (hN' k j)

lemma Ft_nonneg (hc : ∀ k, 0 ≤ c k) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (k : ℕ) (i j : Fin 3) :
    0 ≤ Ft a b c k i j := by
  have := hc k; have := ha k; have := hb k
  fin_cases i <;> fin_cases j <;> simp [Ft] <;> assumption

lemma Ft_mulVec (k : ℕ) (x : Fin 3 → ℝ) : Ft a b c k *ᵥ x = ![c k * x 2, a k * x 0, b k * x 1] := by
  ext i
  fin_cases i <;> simp [Ft, mulVec, dotProduct, Fin.sum_univ_three]

lemma det_Ft_zero : det (Ft a b c 0) = a 0 * b 0 * c 0 := by
  rw [det_fin_three]
  simp [Ft]
  ring

section Y

variable {a b c} {M : Matrix (Fin 3) (Fin 3) ℝ} (h : Sub M (phi a b c))
include h

lemma Yof_nonneg (i j : Fin 3) : 0 ≤ Yof a b c M i j := by
  have hp0 := h.pos 0; have hp1 := h.pos 1; have hp2 := h.pos 2
  simp only [phi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hp0 hp1 hp2
  have hF : ∀ i j, 0 ≤ Ft a b c 0 i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Ft] <;> linarith
  simp only [Yof, Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.2 h.det_pos.le) (mul_nonneg_entries h.adj_nonneg hF i j)

/-- `Yof M` solves `(1 - M) x = F₀ y` -/
lemma Yof_solve {x y : Fin 3 → ℝ} (hxy : Ft a b c 0 *ᵥ y = (1 - M) *ᵥ x) : Yof a b c M *ᵥ y = x := by
  have hd := h.det_pos.ne'
  rw [Yof, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hxy, Matrix.mulVec_mulVec, adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ hd, one_smul]

lemma det_Yof : det (Yof a b c M) = a 0 * b 0 * c 0 / det (1 - M) := by
  have hd := h.det_pos.ne'
  rw [Yof, det_smul, det_mul, det_adjugate, det_Ft_zero]
  simp only [Fintype.card_fin]
  field_simp

lemma det_Yof_pos : 0 < det (Yof a b c M) := by
  have hp0 := h.pos 0; have hp1 := h.pos 1; have hp2 := h.pos 2
  simp only [phi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hp0 hp1 hp2
  rw [det_Yof h]
  exact div_pos (mul_pos (mul_pos hp1 hp2) hp0) h.det_pos

omit h in
/-- row sums of `Yof M` -/
lemma Yof_one_eq (i : Fin 3) :
    (Yof a b c M *ᵥ 1) i = (det (1 - M))⁻¹ * (adjugate (1 - M) *ᵥ phi a b c) i := by
  have hF : Ft a b c 0 *ᵥ 1 = phi a b c := by
    rw [Ft_mulVec]; simp [phi]
  rw [Yof, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hF]
  simp

lemma Yof_one_le (i : Fin 3) : (Yof a b c M *ᵥ 1) i ≤ 1 := by
  have hd := h.det_pos
  have h1 : adjugate (1 - M) *ᵥ ((1 - M) *ᵥ 1) = det (1 - M) • (1 : Fin 3 → ℝ) := by
    rw [Matrix.mulVec_mulVec, adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 : ∀ j, phi a b c j ≤ ((1 - M) *ᵥ 1) j := by
    intro j
    have hr := h.row j
    have e : ((1 - M) *ᵥ 1) j = 1 - (M j 0 + M j 1 + M j 2) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      simp [mulVec, dotProduct, Fin.sum_univ_three]
    rw [e]; linarith
  have h3 := mulVec_mono h.adj_nonneg h2 i
  rw [h1] at h3
  simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at h3
  rw [Yof_one_eq i, inv_mul_le_iff₀ hd]
  linarith

lemma Yof_one_ge (i : Fin 3) : det (Yof a b c M) ≤ (Yof a b c M *ᵥ 1) i := by
  have hd := h.det_pos
  have hp0 := h.pos 0; have hp1 := h.pos 1; have hp2 := h.pos 2
  obtain ⟨d0, d1, d2⟩ := h.adj_diag
  have n := h.adj_nonneg
  rw [Yof_one_eq i, det_Yof h, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hd.le)
  simp only [phi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hp0 hp1 hp2 d0 d1 d2
  simp only [mulVec, dotProduct, Fin.sum_univ_three, phi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  fin_cases i
  · have := mul_le_mul_of_nonneg_right d0 hp0.le
    have := mul_nonneg (n 0 1) hp1.le
    have := mul_nonneg (n 0 2) hp2.le
    simp only [Fin.zero_eta] at *
    nlinarith
  · have := mul_le_mul_of_nonneg_right d1 hp1.le
    have := mul_nonneg (n 1 0) hp0.le
    have := mul_nonneg (n 1 2) hp2.le
    simp only [Fin.mk_one] at *
    nlinarith
  · have := mul_le_mul_of_nonneg_right d2 hp2.le
    have := mul_nonneg (n 2 0) hp0.le
    have := mul_nonneg (n 2 1) hp1.le
    simp only [Fin.reduceFinMk] at *
    nlinarith

end Y

/-- `E01 x = (x 1, 0, 0)` -/
def E01 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 0; 0, 0, 0]

lemma E01_mulVec (x : Fin 3 → ℝ) : E01 *ᵥ x = ![x 1, 0, 0] := by
  ext i
  fin_cases i <;> simp [E01, mulVec, dotProduct, Fin.sum_univ_three]

lemma E01_nonneg (i j : Fin 3) : 0 ≤ E01 i j := by
  fin_cases i <;> fin_cases j <;> simp [E01]

/-- return matrix at level `u`, from the passage matrices `g v` (from level `v` up to level `u`) -/
noncomputable def Mof (g : ℕ → Matrix (Fin 3) (Fin 3) ℝ) (u : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ k ∈ Ico 1 u, Ft a b c k * g (u + 1 - k) + (c u * b 0) • (E01 * g 2)

/-- passage matrices: `Gs u v` goes from level `v` up to level `u` -/
noncomputable def Gs : ℕ → ℕ → Matrix (Fin 3) (Fin 3) ℝ
  | 0 => fun _ => 1
  | u + 1 => fun v => if v ≤ u then Gs u v * Yof a b c (Mof a b c (Gs u) u) else 1

/-- return matrix at level `u` -/
noncomputable def Mh (u : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := Mof a b c (Gs a b c u) u

/-- passage matrix from level `u` to level `u + 1` -/
noncomputable def Yh (u : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := Yof a b c (Mh a b c u)

lemma Gs_succ_of_le {u v : ℕ} (h : v ≤ u) : Gs a b c (u + 1) v = Gs a b c u v * Yh a b c u := by
  simp [Gs, Mh, Yh, h]

lemma Gs_self (u : ℕ) : Gs a b c u u = 1 := by
  cases u with
  | zero => rfl
  | succ u => simp [Gs]

/-- the standing assumptions on the three sequences -/
structure Hyp : Prop where
  a_nonneg : ∀ k, 0 ≤ a k
  b_nonneg : ∀ k, 0 ≤ b k
  c_nonneg : ∀ k, 0 ≤ c k
  a_sum : ∀ m, ∑ k ∈ range m, a k ≤ 1
  b_sum : ∀ m, ∑ k ∈ range m, b k ≤ 1
  c_sum : ∀ m, ∑ k ∈ range m, c k ≤ 1
  a_pos : 0 < a 0
  b_pos : 0 < b 0
  c_pos : 0 < c 0

lemma row_eq (M : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) : M i 0 + M i 1 + M i 2 = (M *ᵥ 1) i := by
  simp [mulVec, dotProduct, Fin.sum_univ_three]

lemma sum_Ico_one_le {f : ℕ → ℝ} (hs : ∀ m, ∑ k ∈ range m, f k ≤ 1) (u : ℕ) :
    ∑ k ∈ Ico 1 u, f k ≤ 1 - f 0 := by
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · have := hs 1
    simp at this ⊢
    linarith
  · have h1 := hs u
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hu] at h1
    simpa using (by linarith : ∑ k ∈ Ico (0 + 1) u, f k ≤ 1 - f 0)

variable {a b c}

lemma Mh_sub (H : Hyp a b c) {u : ℕ} (hu : 2 ≤ u)
    (IH : ∀ v, 2 ≤ v → v ≤ u →
      (∀ i j, 0 ≤ Gs a b c u v i j) ∧ ∀ i, (Gs a b c u v *ᵥ 1) i ≤ 1) :
    Sub (Mh a b c u) (phi a b c) := by
  have hF := Ft_nonneg a b c H.c_nonneg H.a_nonneg H.b_nonneg
  have hb1 : b 0 ≤ 1 := by simpa using H.b_sum 1
  have hk : ∀ k ∈ Ico 1 u, 2 ≤ u + 1 - k ∧ u + 1 - k ≤ u := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp only [Mh, Mof, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    refine add_nonneg (Finset.sum_nonneg fun k hk' => ?_) ?_
    · exact mul_nonneg_entries (hF k) (IH _ (hk k hk').1 (hk k hk').2).1 i j
    · exact mul_nonneg (mul_nonneg (H.c_nonneg u) H.b_pos.le)
        (mul_nonneg_entries E01_nonneg (IH 2 le_rfl hu).1 i j)
  · intro i
    fin_cases i <;> simp [phi, H.a_pos, H.b_pos, H.c_pos]
  · intro i
    rw [row_eq]
    have hG : ∀ k ∈ Ico 1 u, ∀ j, (Gs a b c u (u + 1 - k) *ᵥ 1) j ≤ 1 := fun k hk' j =>
      (IH _ (hk k hk').1 (hk k hk').2).2 j
    have hG2 : ∀ j, (Gs a b c u 2 *ᵥ 1) j ≤ 1 := fun j => (IH 2 le_rfl hu).2 j
    have hcu := H.c_nonneg u
    fin_cases i
    · have e : (Mh a b c u *ᵥ 1) 0 = ∑ k ∈ Ico 1 u, c k * (Gs a b c u (u + 1 - k) *ᵥ 1) 2 +
          c u * b 0 * (Gs a b c u 2 *ᵥ 1) 1 := by
        simp [Mh, Mof, Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
          Ft_mulVec, E01_mulVec, Finset.sum_apply]
      have s1 : ∑ k ∈ Ico 1 u, c k * (Gs a b c u (u + 1 - k) *ᵥ 1) 2 ≤ ∑ k ∈ Ico 1 u, c k :=
        Finset.sum_le_sum fun k hk' => by
          have := mul_le_mul_of_nonneg_left (hG k hk' 2) (H.c_nonneg k)
          linarith
      have s2 : c u * b 0 * (Gs a b c u 2 *ᵥ 1) 1 ≤ c u := by
        have h1 := mul_le_mul_of_nonneg_left (hG2 1) (mul_nonneg hcu H.b_pos.le)
        have h2 := mul_le_mul_of_nonneg_left hb1 hcu
        linarith
      have h3 := sum_Ico_one_le H.c_sum (u + 1)
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ u)] at h3
      simp only [Fin.zero_eta, phi, Matrix.cons_val_zero]
      rw [e]
      linarith
    · have e : (Mh a b c u *ᵥ 1) 1 = ∑ k ∈ Ico 1 u, a k * (Gs a b c u (u + 1 - k) *ᵥ 1) 0 := by
        simp [Mh, Mof, Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
          Ft_mulVec, E01_mulVec, Finset.sum_apply]
      have s1 : ∑ k ∈ Ico 1 u, a k * (Gs a b c u (u + 1 - k) *ᵥ 1) 0 ≤ ∑ k ∈ Ico 1 u, a k :=
        Finset.sum_le_sum fun k hk' => by
          have := mul_le_mul_of_nonneg_left (hG k hk' 0) (H.a_nonneg k)
          linarith
      have h3 := sum_Ico_one_le H.a_sum u
      simp only [Fin.mk_one, phi, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [e]
      linarith
    · have e : (Mh a b c u *ᵥ 1) 2 = ∑ k ∈ Ico 1 u, b k * (Gs a b c u (u + 1 - k) *ᵥ 1) 1 := by
        simp [Mh, Mof, Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
          Ft_mulVec, E01_mulVec, Finset.sum_apply]
      have s1 : ∑ k ∈ Ico 1 u, b k * (Gs a b c u (u + 1 - k) *ᵥ 1) 1 ≤ ∑ k ∈ Ico 1 u, b k :=
        Finset.sum_le_sum fun k hk' => by
          have := mul_le_mul_of_nonneg_left (hG k hk' 1) (H.b_nonneg k)
          linarith
      have h3 := sum_Ico_one_le H.b_sum u
      have e2 : phi a b c (2 : Fin 3) = b 0 := by simp [phi]
      show (Mh a b c u *ᵥ 1) (2 : Fin 3) ≤ 1 - phi a b c (2 : Fin 3)
      rw [e, e2]
      linarith

/-- the invariant: passage matrices are nonnegative with row sums at most one -/
lemma Gs_inv (H : Hyp a b c) : ∀ u, 2 ≤ u → ∀ v, 2 ≤ v → v ≤ u →
    (∀ i j, 0 ≤ Gs a b c u v i j) ∧ ∀ i, (Gs a b c u v *ᵥ 1) i ≤ 1 := by
  intro u hu
  induction u, hu using Nat.le_induction with
  | base =>
    intro v hv hv'
    have : v = 2 := le_antisymm hv' hv
    subst this
    rw [Gs_self]
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · rw [Matrix.one_apply]; split_ifs <;> norm_num
    · rw [Matrix.one_mulVec]; simp
  | succ u hu IH =>
    intro v hv hv'
    have hS := Mh_sub H hu IH
    rcases Nat.lt_or_ge u v with h | h
    · have : v = u + 1 := by omega
      subst this
      rw [Gs_self]
      refine ⟨fun i j => ?_, fun i => ?_⟩
      · rw [Matrix.one_apply]; split_ifs <;> norm_num
      · rw [Matrix.one_mulVec]; simp
    · rw [Gs_succ_of_le a b c h]
      obtain ⟨n1, n2⟩ := IH v hv h
      refine ⟨mul_nonneg_entries n1 (Yof_nonneg hS), fun i => ?_⟩
      rw [← Matrix.mulVec_mulVec]
      exact le_trans (mulVec_mono n1 (Yof_one_le hS) i) (n2 i)

lemma Mh_sub' (H : Hyp a b c) {u : ℕ} (hu : 2 ≤ u) : Sub (Mh a b c u) (phi a b c) :=
  Mh_sub H hu (Gs_inv H u hu)

/-- sequences of vectors satisfying the recursion of the reversed walk that is killed below level two,
except at the state of phase `2` on level one -/
def IsTH (a b c : ℕ → ℝ) (φ : ℕ → Fin 3 → ℝ) : Prop :=
  ∀ u, 2 ≤ u → Ft a b c 0 *ᵥ φ (u + 1) =
    φ u - ∑ k ∈ Ico 1 u, Ft a b c k *ᵥ φ (u + 1 - k) - (c u * b 0) • (E01 *ᵥ φ 2)

lemma th_aux (H : Hyp a b c) {φ : ℕ → Fin 3 → ℝ} (hφ : IsTH a b c φ) {u : ℕ} (hu : 2 ≤ u)
    (C : ∀ v, 2 ≤ v → v ≤ u → φ v = Gs a b c u v *ᵥ φ u) : φ u = Yh a b c u *ᵥ φ (u + 1) := by
  have hS := Mh_sub' H hu
  have e : Mh a b c u *ᵥ φ u =
      ∑ k ∈ Ico 1 u, Ft a b c k *ᵥ φ (u + 1 - k) + (c u * b 0) • (E01 *ᵥ φ 2) := by
    simp only [Mh, Mof, Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_Ico] at hk
      rw [← Matrix.mulVec_mulVec, ← C (u + 1 - k) (by omega) (by omega)]
    · rw [← Matrix.mulVec_mulVec, ← C 2 le_rfl hu]
  have h1 : Ft a b c 0 *ᵥ φ (u + 1) = (1 - Mh a b c u) *ᵥ φ u := by
    rw [hφ u hu, Matrix.sub_mulVec, Matrix.one_mulVec, e]
    abel
  exact (Yof_solve hS h1).symm

lemma th_passage (H : Hyp a b c) {φ : ℕ → Fin 3 → ℝ} (hφ : IsTH a b c φ) :
    ∀ u, 2 ≤ u → ∀ v, 2 ≤ v → v ≤ u → φ v = Gs a b c u v *ᵥ φ u := by
  intro u hu
  induction u, hu using Nat.le_induction with
  | base =>
    intro v hv hv'
    have : v = 2 := le_antisymm hv' hv
    subst this
    rw [Gs_self, Matrix.one_mulVec]
  | succ u hu IH =>
    intro v hv hv'
    rcases Nat.lt_or_ge u v with h | h
    · have : v = u + 1 := by omega
      subst this
      rw [Gs_self, Matrix.one_mulVec]
    · rw [Gs_succ_of_le a b c h, ← Matrix.mulVec_mulVec, ← th_aux H hφ hu IH]
      exact IH v hv h

lemma th_step (H : Hyp a b c) {φ : ℕ → Fin 3 → ℝ} (hφ : IsTH a b c φ) {u : ℕ} (hu : 2 ≤ u) :
    φ u = Yh a b c u *ᵥ φ (u + 1) :=
  th_aux H hφ hu (th_passage H hφ u hu)

variable (a b c)

/-- the denominator `abc - X³` -/
noncomputable def Qs : PowerSeries ℝ :=
  PowerSeries.mk a * PowerSeries.mk b * PowerSeries.mk c - PowerSeries.X ^ 3

noncomputable def ws : PowerSeries ℝ := (Qs a b c)⁻¹

noncomputable def H0 : PowerSeries ℝ := PowerSeries.mk a * PowerSeries.mk b * PowerSeries.mk c * ws a b c
noncomputable def H1 : PowerSeries ℝ := PowerSeries.X ^ 2 * PowerSeries.mk a * ws a b c
noncomputable def H2 : PowerSeries ℝ := PowerSeries.X * PowerSeries.mk a * PowerSeries.mk b * ws a b c

lemma constCoeff_Qs : PowerSeries.constantCoeff (Qs a b c) = a 0 * b 0 * c 0 := by
  simp [Qs]

variable {a b c}

lemma Qs_mul_ws (h0 : a 0 * b 0 * c 0 ≠ 0) : Qs a b c * ws a b c = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [constCoeff_Qs]; exact h0)

lemma H0_eq (h0 : a 0 * b 0 * c 0 ≠ 0) : H0 a b c = 1 + PowerSeries.X ^ 3 * ws a b c := by
  have := Qs_mul_ws h0
  rw [Qs, sub_mul] at this
  rw [H0]
  linear_combination this

lemma rel0 : PowerSeries.X * H0 a b c = PowerSeries.mk c * H2 a b c := by
  rw [H0, H2]; ring

lemma rel1 (h0 : a 0 * b 0 * c 0 ≠ 0) : PowerSeries.X * H1 a b c = PowerSeries.mk a * (H0 a b c - 1) := by
  rw [H0_eq h0, H1]; ring

lemma rel2 : PowerSeries.X * H2 a b c = PowerSeries.mk b * H1 a b c := by
  rw [H1, H2]; ring

/-- coefficient form of a relation `X * F = mk f * G` -/
lemma coeff_rel {f : ℕ → ℝ} {F G : PowerSeries ℝ} (h : PowerSeries.X * F = PowerSeries.mk f * G) (m : ℕ) :
    PowerSeries.coeff m F = ∑ k ∈ range (m + 2), f k * PowerSeries.coeff (m + 1 - k) G := by
  have := congrArg (PowerSeries.coeff (m + 1)) h
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i (PowerSeries.mk f) * PowerSeries.coeff j G)] at this
  simpa using this


variable (a b c)

/-- coefficients of the three generating functions: the values of the harmonic function of the reversed
walk that starts from `(1, 0, 0)` on level zero -/
noncomputable def h0 (n : ℕ) : ℝ := PowerSeries.coeff n (H0 a b c)
noncomputable def h1 (n : ℕ) : ℝ := PowerSeries.coeff n (H1 a b c)
noncomputable def h2 (n : ℕ) : ℝ := PowerSeries.coeff n (H2 a b c)

noncomputable def hv (n : ℕ) : Fin 3 → ℝ := ![h0 a b c n, h1 a b c n, h2 a b c n]

lemma hv_zero (n : ℕ) : hv a b c n 0 = h0 a b c n := rfl
lemma hv_one (n : ℕ) : hv a b c n 1 = h1 a b c n := rfl
lemma hv_two (n : ℕ) : hv a b c n 2 = h2 a b c n := rfl

variable {a b c}

lemma cc_H0 (h : a 0 * b 0 * c 0 ≠ 0) : PowerSeries.constantCoeff (H0 a b c) = 1 := by
  rw [H0_eq h]; simp

lemma cc_H1 : PowerSeries.constantCoeff (H1 a b c) = 0 := by
  rw [H1]; simp

lemma cc_H2 : PowerSeries.constantCoeff (H2 a b c) = 0 := by
  rw [H2]; simp [mul_assoc]

lemma h0_zero (h : a 0 * b 0 * c 0 ≠ 0) : h0 a b c 0 = 1 := by
  rw [h0, PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_H0 h]

lemma h1_zero : h1 a b c 0 = 0 := by
  rw [h1, PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_H1]

lemma h2_zero : h2 a b c 0 = 0 := by
  rw [h2, PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_H2]

lemma range_split {F : ℕ → ℝ} {u : ℕ} (hu : 1 ≤ u) :
    ∑ k ∈ range u, F k = F 0 + ∑ k ∈ Ico 1 u, F k := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]

/-- the three one-step relations, with the vanishing last term removed -/
lemma R0 (m : ℕ) : h0 a b c m = ∑ k ∈ range (m + 1), c k * h2 a b c (m + 1 - k) := by
  have := coeff_rel (rel0 (a := a) (b := b) (c := c)) m
  rw [Finset.sum_range_succ, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_H2,
    mul_zero, add_zero] at this
  exact this

lemma R2 (m : ℕ) : h2 a b c m = ∑ k ∈ range (m + 1), b k * h1 a b c (m + 1 - k) := by
  have := coeff_rel (rel2 (a := a) (b := b) (c := c)) m
  rw [Finset.sum_range_succ, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_H1,
    mul_zero, add_zero] at this
  exact this

lemma R1 (h : a 0 * b 0 * c 0 ≠ 0) (m : ℕ) :
    h1 a b c m = ∑ k ∈ range (m + 1), a k * h0 a b c (m + 1 - k) := by
  have := coeff_rel (rel1 h) m
  have e0 : PowerSeries.coeff 0 (H0 a b c - 1) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, cc_H0 h, map_one, sub_self]
  have e1 : ∀ k ∈ range (m + 1), a k * PowerSeries.coeff (m + 1 - k) (H0 a b c - 1) =
      a k * h0 a b c (m + 1 - k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hne : m + 1 - k ≠ 0 := by omega
    rw [map_sub, PowerSeries.coeff_one, if_neg hne, sub_zero]
    rfl
  rw [Finset.sum_range_succ, Nat.sub_self, e0, mul_zero, add_zero, Finset.sum_congr rfl e1] at this
  exact this

/-- the values on levels one and two -/
lemma h_vals (H : Hyp a b c) :
    h0 a b c 1 = 0 ∧ h1 a b c 1 = 0 ∧ h2 a b c 1 = 1 / c 0 ∧
      h0 a b c 2 = 0 ∧ h1 a b c 2 = 1 / (b 0 * c 0) ∧ h2 a b c 2 = -(c 1 / c 0 ^ 2) := by
  have ha := H.a_pos; have hb := H.b_pos; have hc := H.c_pos
  have h : a 0 * b 0 * c 0 ≠ 0 := by positivity
  have e00 := R0 (a := a) (b := b) (c := c) 0
  have e10 := R1 h 0
  have e20 := R2 (a := a) (b := b) (c := c) 0
  have e01 := R0 (a := a) (b := b) (c := c) 1
  have e11 := R1 h 1
  have e21 := R2 (a := a) (b := b) (c := c) 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero,
    Nat.reduceAdd, Nat.reduceSub] at e00 e10 e20 e01 e11 e21
  rw [h0_zero h] at e00
  rw [h1_zero] at e10
  rw [h2_zero] at e20
  have v21 : h2 a b c 1 = 1 / c 0 := by field_simp; linarith
  have v01 : h0 a b c 1 = 0 := by
    rcases mul_eq_zero.1 e10.symm with h' | h'
    · exact absurd h' ha.ne'
    · exact h'
  have v11 : h1 a b c 1 = 0 := by
    rcases mul_eq_zero.1 e20.symm with h' | h'
    · exact absurd h' hb.ne'
    · exact h'
  rw [v01, v21] at e01
  rw [v11, v01] at e11
  rw [v21, v11] at e21
  have v02 : h0 a b c 2 = 0 := by
    have : a 0 * h0 a b c 2 = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' ha.ne'
    · exact h'
  have v12 : h1 a b c 2 = 1 / (b 0 * c 0) := by
    field_simp
    field_simp at e21
    linarith
  have v22 : h2 a b c 2 = -(c 1 / c 0 ^ 2) := by
    field_simp
    field_simp at e01
    linarith
  exact ⟨v01, v11, v21, v02, v12, v22⟩

/-- a componentwise criterion for `IsTH` -/
lemma isTH_of {φ : ℕ → Fin 3 → ℝ}
    (e0 : ∀ u, 2 ≤ u → c 0 * φ (u + 1) 2 =
      φ u 0 - ∑ k ∈ Ico 1 u, c k * φ (u + 1 - k) 2 - c u * b 0 * φ 2 1)
    (e1 : ∀ u, 2 ≤ u → a 0 * φ (u + 1) 0 = φ u 1 - ∑ k ∈ Ico 1 u, a k * φ (u + 1 - k) 0)
    (e2 : ∀ u, 2 ≤ u → b 0 * φ (u + 1) 1 = φ u 2 - ∑ k ∈ Ico 1 u, b k * φ (u + 1 - k) 1) :
    IsTH a b c φ := by
  intro u hu
  ext i
  fin_cases i
  · simpa [Ft_mulVec, E01_mulVec, Finset.sum_apply] using e0 u hu
  · simpa [Ft_mulVec, E01_mulVec, Finset.sum_apply] using e1 u hu
  · simpa [Ft_mulVec, E01_mulVec, Finset.sum_apply] using e2 u hu

/-- the harmonic function satisfies the recursion of the killed walk -/
lemma hv_TH (H : Hyp a b c) : IsTH a b c (hv a b c) := by
  have ha := H.a_pos; have hb := H.b_pos; have hc := H.c_pos
  have h : a 0 * b 0 * c 0 ≠ 0 := by positivity
  obtain ⟨v01, v11, v21, v02, v12, v22⟩ := h_vals H
  refine isTH_of ?_ ?_ ?_
  · intro u hu
    simp only [hv_zero, hv_one, hv_two]
    have e := R0 (a := a) (b := b) (c := c) u
    rw [Finset.sum_range_succ, range_split (by omega : 1 ≤ u), Nat.sub_zero,
      show u + 1 - u = 1 by omega, v21] at e
    rw [v12, e]
    field_simp
    ring
  · intro u hu
    simp only [hv_zero, hv_one]
    have e := R1 h u
    rw [Finset.sum_range_succ, range_split (by omega : 1 ≤ u), Nat.sub_zero,
      show u + 1 - u = 1 by omega, v01] at e
    rw [e]; ring
  · intro u hu
    simp only [hv_one, hv_two]
    have e := R2 (a := a) (b := b) (c := c) u
    rw [Finset.sum_range_succ, range_split (by omega : 1 ≤ u), Nat.sub_zero,
      show u + 1 - u = 1 by omega, v11] at e
    rw [e]; ring

/-- so does the same function moved up by one level -/
lemma hv_shift_TH (H : Hyp a b c) : IsTH a b c (fun n => hv a b c (n - 1)) := by
  have ha := H.a_pos; have hb := H.b_pos; have hc := H.c_pos
  have h : a 0 * b 0 * c 0 ≠ 0 := by positivity
  obtain ⟨v01, v11, v21, v02, v12, v22⟩ := h_vals H
  refine isTH_of ?_ ?_ ?_
  · intro u hu
    obtain ⟨m, rfl⟩ : ∃ m, u = m + 1 := ⟨u - 1, by omega⟩
    simp only [hv_zero, hv_one, hv_two, Nat.add_sub_cancel, Nat.reduceSub]
    have e := R0 (a := a) (b := b) (c := c) m
    rw [range_split (by omega : 1 ≤ m + 1), Nat.sub_zero] at e
    have e' : ∑ k ∈ Ico 1 (m + 1), c k * h2 a b c (m + 1 + 1 - k - 1) =
        ∑ k ∈ Ico 1 (m + 1), c k * h2 a b c (m + 1 - k) :=
      Finset.sum_congr rfl fun k hk => by
        rw [Finset.mem_Ico] at hk
        rw [show m + 1 + 1 - k - 1 = m + 1 - k by omega]
    rw [e', v11, e]; ring
  · intro u hu
    obtain ⟨m, rfl⟩ : ∃ m, u = m + 1 := ⟨u - 1, by omega⟩
    simp only [hv_zero, hv_one, Nat.add_sub_cancel]
    have e := R1 h m
    rw [range_split (by omega : 1 ≤ m + 1), Nat.sub_zero] at e
    have e' : ∑ k ∈ Ico 1 (m + 1), a k * h0 a b c (m + 1 + 1 - k - 1) =
        ∑ k ∈ Ico 1 (m + 1), a k * h0 a b c (m + 1 - k) :=
      Finset.sum_congr rfl fun k hk => by
        rw [Finset.mem_Ico] at hk
        rw [show m + 1 + 1 - k - 1 = m + 1 - k by omega]
    rw [e', e]; ring
  · intro u hu
    obtain ⟨m, rfl⟩ : ∃ m, u = m + 1 := ⟨u - 1, by omega⟩
    simp only [hv_one, hv_two, Nat.add_sub_cancel]
    have e := R2 (a := a) (b := b) (c := c) m
    rw [range_split (by omega : 1 ≤ m + 1), Nat.sub_zero] at e
    have e' : ∑ k ∈ Ico 1 (m + 1), b k * h1 a b c (m + 1 + 1 - k - 1) =
        ∑ k ∈ Ico 1 (m + 1), b k * h1 a b c (m + 1 - k) :=
      Finset.sum_congr rfl fun k hk => by
        rw [Finset.mem_Ico] at hk
        rw [show m + 1 + 1 - k - 1 = m + 1 - k by omega]
    rw [e', e]; ring

/-- triple product of three vectors -/
def T3 (x y z : Fin 3 → ℝ) : ℝ :=
  x 0 * (y 1 * z 2 - y 2 * z 1) - x 1 * (y 0 * z 2 - y 2 * z 0) + x 2 * (y 0 * z 1 - y 1 * z 0)

lemma T3_mulVec (Y : Matrix (Fin 3) (Fin 3) ℝ) (x y z : Fin 3 → ℝ) :
    T3 (Y *ᵥ x) (Y *ᵥ y) (Y *ᵥ z) = det Y * T3 x y z := by
  simp only [T3, det_fin_three, mulVec, dotProduct, Fin.sum_univ_three]
  ring

lemma T3_split (x : Fin 3 → ℝ) (r : ℝ) (y z : Fin 3 → ℝ) :
    T3 x y z = T3 (x - r • 1) y z + r * T3 1 y z := by
  simp only [T3, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
  ring

lemma step_eqs (H : Hyp a b c) {n : ℕ} (hn : 1 ≤ n) :
    hv a b c (n + 1) = Yh a b c (n + 1) *ᵥ hv a b c (n + 2) ∧
      hv a b c n = Yh a b c (n + 1) *ᵥ hv a b c (n + 1) := by
  refine ⟨th_step H (hv_TH H) (by omega), ?_⟩
  have := th_step H (hv_shift_TH H) (u := n + 1) (by omega)
  simpa using this

lemma K_base (H : Hyp a b c) (x : Fin 3 → ℝ) :
    T3 x (hv a b c 2) (hv a b c 1) = x 0 * (1 / (b 0 * c 0) * (1 / c 0)) := by
  obtain ⟨v01, v11, v21, v02, v12, v22⟩ := h_vals H
  simp only [T3, hv_zero, hv_one, hv_two, v01, v11, v21, v02, v12, v22]
  ring

lemma K_nonneg (H : Hyp a b c) : ∀ n, 1 ≤ n → ∀ x : Fin 3 → ℝ, (∀ i, 0 ≤ x i) →
    0 ≤ T3 x (hv a b c (n + 1)) (hv a b c n) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro x hx
    have ha := H.a_pos; have hb := H.b_pos; have hc := H.c_pos
    rw [K_base H]
    have := hx 0
    positivity
  | succ n hn IH =>
    intro x hx
    have hS := Mh_sub' H (by omega : 2 ≤ n + 1)
    obtain ⟨e1, e2⟩ := step_eqs H hn
    have h1 := IH (Yh a b c (n + 1) *ᵥ x) (mulVec_nonneg (Yof_nonneg hS) hx)
    have key : T3 (Yh a b c (n + 1) *ᵥ x) (hv a b c (n + 1)) (hv a b c n) =
        det (Yh a b c (n + 1)) * T3 x (hv a b c (n + 2)) (hv a b c (n + 1)) := by
      rw [← T3_mulVec, ← e1, ← e2]
    rw [key] at h1
    exact (mul_nonneg_iff_of_pos_left (det_Yof_pos hS)).1 h1

lemma K_mono (H : Hyp a b c) {n : ℕ} (hn : 1 ≤ n) :
    T3 1 (hv a b c (n + 1)) (hv a b c n) ≤ T3 1 (hv a b c (n + 2)) (hv a b c (n + 1)) := by
  have hS := Mh_sub' H (by omega : 2 ≤ n + 1)
  obtain ⟨e1, e2⟩ := step_eqs H hn
  have hd := det_Yof_pos hS
  have key : T3 (Yh a b c (n + 1) *ᵥ 1) (hv a b c (n + 1)) (hv a b c n) =
      det (Yh a b c (n + 1)) * T3 1 (hv a b c (n + 2)) (hv a b c (n + 1)) := by
    rw [← T3_mulVec, ← e1, ← e2]
  have h2 := K_nonneg H n hn (Yh a b c (n + 1) *ᵥ 1 - det (Yh a b c (n + 1)) • 1) (by
    intro i
    have := Yof_one_ge hS i
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact sub_nonneg.2 this)
  rw [T3_split _ (det (Yh a b c (n + 1)))] at key
  have h3 : det (Yh a b c (n + 1)) * T3 1 (hv a b c (n + 1)) (hv a b c n) ≤
      det (Yh a b c (n + 1)) * T3 1 (hv a b c (n + 2)) (hv a b c (n + 1)) := by linarith
  exact le_of_mul_le_mul_left h3 hd

lemma K_pos (H : Hyp a b c) : ∀ n, 1 ≤ n → 0 < T3 1 (hv a b c (n + 1)) (hv a b c n) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    have ha := H.a_pos; have hb := H.b_pos; have hc := H.c_pos
    rw [K_base H]
    simp only [Pi.one_apply]
    positivity
  | succ n hn IH => exact lt_of_lt_of_le IH (K_mono H hn)

section link

variable (s α β : ℕ → ℝ)

lemma coeff_one_mul' (φ ψ : PowerSeries ℝ) :
    PowerSeries.coeff 1 (φ * ψ) =
      PowerSeries.coeff 0 φ * PowerSeries.coeff 1 ψ + PowerSeries.coeff 1 φ * PowerSeries.coeff 0 ψ := by
  rw [PowerSeries.coeff_mul]
  simp [Finset.Nat.antidiagonal_succ]

/-- the generating function of the first sequence -/
lemma alpha_key (H : Hyp a b c)
    (hs : ∀ n, s n = PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b * PowerSeries.mk c))
    (hα0 : α 0 = 1) (hα1 : α 1 = 0) (hα2 : α 2 = -(1 / (b 0 * c 0)))
    (hα : ∀ n, 3 ≤ n → α n = 1 / s 0 * (α (n - 3) - a (n - 2) - ∑ k ∈ Ico 1 n, s k * α (n - k))) :
    Qs a b c * PowerSeries.mk α =
      PowerSeries.mk a * PowerSeries.mk b * PowerSeries.mk c - PowerSeries.X ^ 2 * PowerSeries.mk a := by
  have ha := H.a_pos; have hb := H.b_pos; have hc := H.c_pos
  have hs0 : s 0 = a 0 * b 0 * c 0 := by rw [hs]; simp
  have hs0' : s 0 ≠ 0 := by rw [hs0]; positivity
  ext n
  have eL : PowerSeries.coeff n (Qs a b c * PowerSeries.mk α) =
      ∑ k ∈ range (n + 1), s k * α (n - k) - (if 3 ≤ n then α (n - 3) else 0) := by
    rw [Qs, sub_mul, map_sub, PowerSeries.coeff_mul, PowerSeries.coeff_X_pow_mul',
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
        PowerSeries.coeff i (PowerSeries.mk a * PowerSeries.mk b * PowerSeries.mk c) *
          PowerSeries.coeff j (PowerSeries.mk α))]
    simp only [PowerSeries.coeff_mk, ← hs]
  have eR : PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b * PowerSeries.mk c -
      PowerSeries.X ^ 2 * PowerSeries.mk a) = s n - (if 2 ≤ n then a (n - 2) else 0) := by
    rw [map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk, ← hs]
  rw [eL, eR]
  match n with
  | 0 => simp [hα0]
  | 1 => simp [Finset.sum_range_succ, hα0, hα1]
  | 2 =>
    simp [Finset.sum_range_succ, hα0, hα1, hα2, hs0]
    field_simp
    ring
  | n + 3 =>
    have h3 := hα (n + 3) (by omega)
    have h3' : s 0 * α (n + 3) =
        α (n + 3 - 3) - a (n + 3 - 2) - ∑ k ∈ Ico 1 (n + 3), s k * α (n + 3 - k) := by
      rw [h3]; field_simp
    rw [Finset.sum_range_succ, range_split (by omega : 1 ≤ n + 3), Nat.sub_zero, Nat.sub_self, hα0,
      if_pos (by omega : 3 ≤ n + 3), if_pos (by omega : 2 ≤ n + 3)]
    linarith

/-- the generating function of the second sequence -/
lemma beta_key (H : Hyp a b c)
    (hs : ∀ n, s n = PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b * PowerSeries.mk c))
    (hβ0 : β 0 = 0) (hβ1 : β 1 = 1) (hβ2 : β 2 = -(c 1 / c 0) - 1 / b 0)
    (hβ : ∀ n, 3 ≤ n → β n = 1 / s 0 * (β (n - 3) - ∑ k ∈ Ico 1 n, s k * β (n - k) - a (n - 2) * c 0 +
      c 0 * ∑ k ∈ range n, a k * b (n - 1 - k))) :
    Qs a b c * PowerSeries.mk β =
      PowerSeries.C (c 0) * (PowerSeries.X * (PowerSeries.mk a * PowerSeries.mk b) -
        PowerSeries.X ^ 2 * PowerSeries.mk a) := by
  have ha := H.a_pos; have hb := H.b_pos; have hc := H.c_pos
  have hs0 : s 0 = a 0 * b 0 * c 0 := by rw [hs]; simp
  have hs0' : s 0 ≠ 0 := by rw [hs0]; positivity
  have hs1 : s 1 = a 0 * b 0 * c 1 + a 0 * b 1 * c 0 + a 1 * b 0 * c 0 := by
    rw [hs, coeff_one_mul', coeff_one_mul']
    simp
    ring
  have hab : ∀ m, PowerSeries.coeff m (PowerSeries.mk a * PowerSeries.mk b) =
      ∑ k ∈ range (m + 1), a k * b (m - k) := by
    intro m
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
        PowerSeries.coeff i (PowerSeries.mk a) * PowerSeries.coeff j (PowerSeries.mk b))]
    simp only [PowerSeries.coeff_mk]
  ext n
  have eL : PowerSeries.coeff n (Qs a b c * PowerSeries.mk β) =
      ∑ k ∈ range (n + 1), s k * β (n - k) - (if 3 ≤ n then β (n - 3) else 0) := by
    rw [Qs, sub_mul, map_sub, PowerSeries.coeff_mul, PowerSeries.coeff_X_pow_mul',
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
        PowerSeries.coeff i (PowerSeries.mk a * PowerSeries.mk b * PowerSeries.mk c) *
          PowerSeries.coeff j (PowerSeries.mk β))]
    simp only [PowerSeries.coeff_mk, ← hs]
  rw [eL, PowerSeries.coeff_C_mul, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk]
  match n with
  | 0 => simp [hβ0]
  | 1 =>
    rw [PowerSeries.coeff_succ_X_mul, hab]
    simp [Finset.sum_range_succ, hβ0, hβ1, hs0]
    ring
  | 2 =>
    rw [PowerSeries.coeff_succ_X_mul, hab]
    simp [Finset.sum_range_succ, hβ0, hβ1, hβ2, hs0, hs1]
    field_simp
    ring
  | n + 3 =>
    have h3 := hβ (n + 3) (by omega)
    have h3' : s 0 * β (n + 3) = β (n + 3 - 3) - ∑ k ∈ Ico 1 (n + 3), s k * β (n + 3 - k) -
        a (n + 3 - 2) * c 0 + c 0 * ∑ k ∈ range (n + 3), a k * b (n + 3 - 1 - k) := by
      rw [h3]; field_simp
    rw [PowerSeries.coeff_succ_X_mul, hab, Finset.sum_range_succ (fun k => s k * β (n + 3 - k)),
      range_split (by omega : 1 ≤ n + 3), Nat.sub_zero, Nat.sub_self, hβ0,
      if_pos (by omega : 3 ≤ n + 3), if_pos (by omega : 2 ≤ n + 3)]
    have e : ∑ k ∈ range (n + 3), a k * b (n + 3 - 1 - k) = ∑ k ∈ range (n + 2 + 1), a k * b (n + 2 - k) :=
      rfl
    rw [e] at h3'
    linarith

/-- the two sequences in terms of the harmonic function -/
lemma alpha_eq (H : Hyp a b c)
    (hs : ∀ n, s n = PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b * PowerSeries.mk c))
    (hα0 : α 0 = 1) (hα1 : α 1 = 0) (hα2 : α 2 = -(1 / (b 0 * c 0)))
    (hα : ∀ n, 3 ≤ n → α n = 1 / s 0 * (α (n - 3) - a (n - 2) - ∑ k ∈ Ico 1 n, s k * α (n - k)))
    (n : ℕ) : α n = h0 a b c n - h1 a b c n := by
  have ha := H.a_pos; have hb := H.b_pos; have hc := H.c_pos
  have h : a 0 * b 0 * c 0 ≠ 0 := by positivity
  have key := alpha_key s α H hs hα0 hα1 hα2 hα
  have hq := Qs_mul_ws h
  have e : PowerSeries.mk α = H0 a b c - H1 a b c := by
    have : PowerSeries.mk α = ws a b c * (Qs a b c * PowerSeries.mk α) := by
      rw [← mul_assoc, mul_comm (ws a b c), hq, one_mul]
    rw [this, key, H0, H1]
    ring
  have := congrArg (PowerSeries.coeff n) e
  rw [PowerSeries.coeff_mk, map_sub] at this
  exact this

lemma beta_eq (H : Hyp a b c)
    (hs : ∀ n, s n = PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b * PowerSeries.mk c))
    (hβ0 : β 0 = 0) (hβ1 : β 1 = 1) (hβ2 : β 2 = -(c 1 / c 0) - 1 / b 0)
    (hβ : ∀ n, 3 ≤ n → β n = 1 / s 0 * (β (n - 3) - ∑ k ∈ Ico 1 n, s k * β (n - k) - a (n - 2) * c 0 +
      c 0 * ∑ k ∈ range n, a k * b (n - 1 - k)))
    (n : ℕ) : β n = c 0 * (h2 a b c n - h1 a b c n) := by
  have ha := H.a_pos; have hb := H.b_pos; have hc := H.c_pos
  have h : a 0 * b 0 * c 0 ≠ 0 := by positivity
  have key := beta_key s β H hs hβ0 hβ1 hβ2 hβ
  have hq := Qs_mul_ws h
  have e : PowerSeries.mk β = PowerSeries.C (c 0) * (H2 a b c - H1 a b c) := by
    have : PowerSeries.mk β = ws a b c * (Qs a b c * PowerSeries.mk β) := by
      rw [← mul_assoc, mul_comm (ws a b c), hq, one_mul]
    rw [this, key, H1, H2]
    ring
  have := congrArg (PowerSeries.coeff n) e
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, map_sub] at this
  exact this

/-- **The determinants are positive and do not decrease.** -/
theorem core (H : Hyp a b c)
    (hs : ∀ n, s n = PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b * PowerSeries.mk c))
    (hα0 : α 0 = 1) (hα1 : α 1 = 0) (hα2 : α 2 = -(1 / (b 0 * c 0)))
    (hα : ∀ n, 3 ≤ n → α n = 1 / s 0 * (α (n - 3) - a (n - 2) - ∑ k ∈ Ico 1 n, s k * α (n - k)))
    (hβ0 : β 0 = 0) (hβ1 : β 1 = 1) (hβ2 : β 2 = -(c 1 / c 0) - 1 / b 0)
    (hβ : ∀ n, 3 ≤ n → β n = 1 / s 0 * (β (n - 3) - ∑ k ∈ Ico 1 n, s k * β (n - k) - a (n - 2) * c 0 +
      c 0 * ∑ k ∈ range n, a k * b (n - 1 - k)))
    (n : ℕ) :
    0 < α n * β (n + 1) - α (n + 1) * β n ∧
      α n * β (n + 1) - α (n + 1) * β n ≤ α (n + 1) * β (n + 2) - α (n + 2) * β (n + 1) := by
  have ha := H.a_pos; have hb := H.b_pos; have hc := H.c_pos
  have hb1 : b 0 ≤ 1 := by simpa using H.b_sum 1
  have hc1 : c 0 ≤ 1 := by simpa using H.c_sum 1
  have hA := alpha_eq s α H hs hα0 hα1 hα2 hα
  have hB := beta_eq s β H hs hβ0 hβ1 hβ2 hβ
  have hD : ∀ m, α m * β (m + 1) - α (m + 1) * β m =
      c 0 * T3 1 (hv a b c (m + 1)) (hv a b c m) := by
    intro m
    rw [hA m, hA (m + 1), hB m, hB (m + 1)]
    simp only [T3, hv_zero, hv_one, hv_two, Pi.one_apply]
    ring
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have e0 : α 0 * β (0 + 1) - α (0 + 1) * β 0 = 1 := by simp [hα0, hα1, hβ0, hβ1]
    have e1 : α (0 + 1) * β (0 + 2) - α (0 + 2) * β (0 + 1) = 1 / (b 0 * c 0) := by
      simp [hα1, hα2, hβ1]
    rw [e0, e1]
    refine ⟨one_pos, ?_⟩
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · rw [hD n, hD (n + 1)]
    exact ⟨mul_pos hc (K_pos H n hn), mul_le_mul_of_nonneg_left (K_mono H hn) hc.le⟩

end link

section counterexample

open OMA.S_mo_217457

/-- the first claim is a fair coin, the other two claims vanish -/
noncomputable def coinLaw : PMF Claims :=
  (PMF.uniformOfFintype Bool).map fun x => ((if x then 1 else 0 : ℕ), ((0 : ℕ), (0 : ℕ)))

lemma coin_total : mass coinLaw total 0 = 2⁻¹ := by
  simp [mass, coinLaw, PMF.map_comp, PMF.map_apply, total, Function.comp_def, tsum_fintype]

lemma coin_snd : mass coinLaw (fun v => v.2.1) 0 = 1 := by
  have : (fun v : Claims => v.2.1) ∘ (fun x : Bool => ((if x then 1 else 0 : ℕ), ((0 : ℕ), (0 : ℕ)))) =
      Function.const Bool 0 := rfl
  simp [mass, coinLaw, PMF.map_comp, this]

lemma coin_thd : mass coinLaw (fun v => v.2.2) 0 = 1 := by
  have : (fun v : Claims => v.2.2) ∘ (fun x : Bool => ((if x then 1 else 0 : ℕ), ((0 : ℕ), (0 : ℕ)))) =
      Function.const Bool 0 := rfl
  simp [mass, coinLaw, PMF.map_comp, this]

lemma coin_det_zero : detAt coinLaw 1 0 = 1 := by
  simp [detAt, S_mo_217457.alpha, S_mo_217457.beta, seq]

lemma coin_det_one : detAt coinLaw 1 (0 + 1) = 1 := by
  simp [detAt, S_mo_217457.alpha, S_mo_217457.beta, seq, coin_snd, coin_thd]

end counterexample

end OMA

/-- **The claim of the source fails**, already for independent claims: for a fair coin and two claims
that vanish, `D 1 = D 0`. (What holds for all independent claims is `OMA.core`.) -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_217457.main) := by
  intro h
  have hm := OMA.coin_total
  have key := (h OMA.coinLaw (by rw [hm]; norm_num) (by rw [hm]; norm_num) 0).1.2
  rw [OMA.coin_det_zero, OMA.coin_det_one] at key
  exact lt_irrefl _ key

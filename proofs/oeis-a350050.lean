import OMAStatements.S_oeis_a350050
import Mathlib

-- Problem: OEIS A350050, conjectures on the traces of the exterior powers of the matrices
-- A[i,j] = n - |(n+1)/2 - j| - |(n+1)/2 - i| and A[i,j] = (n mod 2) + |(n+1)/2 - j| + |(n+1)/2 - i|.
-- Statement: statements/oeis-a350050.lean (declaration OMA.S_oeis_a350050.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Each of the two matrices has the entries v(i) + v(j) for a vector v = c + e u, where
-- u(i) = |(n+1)/2 - i| and e = -1 or 1. Such a matrix is a product P Q of an n X 2 matrix and a
-- 2 X n matrix, so its characteristic polynomial is x^(n-2) times the characteristic polynomial
-- of the 2 X 2 matrix Q P = [[S1, n], [S2, S1]] with S1 = sum v(i), S2 = sum v(i)^2:
--   x^(n-2) (x^2 - 2 S1 x + (S1^2 - n S2)).
-- So the coefficients of x^(n-k) are 0 for k > 2, and the coefficient of x^(n-2) is
-- S1^2 - n S2 = -(n sum u(i)^2 - (sum u(i))^2). The sum of u(i)^2 is n(n^2-1)/12, and the sum
-- of u(i) is h(h+1) for n = 2h+1 and h^2 for n = 2h; this gives the value a(n), which is not
-- negative (Cauchy-Schwarz).

namespace OMA.A350050

open OMA.S_oeis_a350050 Polynomial Finset

/-- The matrix with the entries `v i + v j`. -/
def Mv {n : ℕ} (v : Fin n → ℚ) : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => v i + v j

def P {n : ℕ} (v : Fin n → ℚ) : Matrix (Fin n) (Fin 2) ℚ :=
  Matrix.of fun i k => if k = 0 then v i else 1

def Q {n : ℕ} (v : Fin n → ℚ) : Matrix (Fin 2) (Fin n) ℚ :=
  Matrix.of fun k j => if k = 0 then 1 else v j

lemma PQ {n : ℕ} (v : Fin n → ℚ) : P v * Q v = Mv v := by
  ext i j
  simp [P, Q, Mv, Matrix.mul_apply, Fin.sum_univ_two]

lemma QP {n : ℕ} (v : Fin n → ℚ) :
    Q v * P v = !![∑ i, v i, (n : ℚ); ∑ i, v i ^ 2, ∑ i, v i] := by
  ext k l
  fin_cases k <;> fin_cases l <;> simp [P, Q, Matrix.mul_apply, pow_two]

lemma charpoly_Mv {n : ℕ} (hn : 2 ≤ n) (v : Fin n → ℚ) :
    (Mv v).charpoly = X ^ (n - 2) *
      (X ^ 2 - C (2 * ∑ i, v i) * X + C ((∑ i, v i) ^ 2 - (n : ℚ) * ∑ i, v i ^ 2)) := by
  have h := Matrix.charpoly_mul_comm_of_le (P v) (Q v) (by simpa using hn)
  rw [PQ, QP, Matrix.charpoly_fin_two] at h
  simp only [Fintype.card_fin] at h
  have ht : (!![∑ i, v i, (n : ℚ); ∑ i, v i ^ 2, ∑ i, v i]).trace = 2 * ∑ i, v i := by
    rw [Matrix.trace_fin_two_of]
    ring
  have hd : (!![∑ i, v i, (n : ℚ); ∑ i, v i ^ 2, ∑ i, v i]).det
      = (∑ i, v i) ^ 2 - (n : ℚ) * ∑ i, v i ^ 2 := by
    rw [Matrix.det_fin_two_of]
    ring
  rw [ht, hd] at h
  exact h

lemma coeff_Mv {n : ℕ} (hn : 2 ≤ n) (v : Fin n → ℚ) :
    (Mv v).charpoly.coeff (n - 2) = (∑ i, v i) ^ 2 - (n : ℚ) * ∑ i, v i ^ 2 ∧
    ∀ k : ℕ, 2 < k → k ≤ n → (Mv v).charpoly.coeff (n - k) = 0 := by
  rw [charpoly_Mv hn v]
  constructor
  · rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_add, coeff_sub, coeff_C_zero,
      coeff_X_pow, coeff_C_mul, coeff_X_zero]
    norm_num
  · intro k hk hkn
    rw [coeff_X_pow_mul', if_neg (by omega)]

lemma sum_lin (c : ℚ) (m : ℕ) : ∑ i ∈ range m, (c - (i : ℚ)) = m * c - (m : ℚ) * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma sum_sq (c : ℚ) (m : ℕ) :
    ∑ i ∈ range m, (c - (i : ℚ)) ^ 2
      = m * c ^ 2 - c * m * (m - 1) + (m - 1) * m * (2 * m - 1) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma sum_half (c : ℚ) (m : ℕ) : ∑ j ∈ range m, ((j : ℚ) + c) = (m : ℚ) * (m - 1) / 2 + m * c := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The sum of |(n-1)/2 - i| over i < n. -/
lemma sum_abs_odd (h : ℕ) :
    ∑ i ∈ range (2 * h + 1), |(h : ℚ) - (i : ℚ)| = (h : ℚ) * (h + 1) := by
  rw [show 2 * h + 1 = h + (h + 1) by ring, Finset.sum_range_add]
  have e1 : ∑ i ∈ range h, |(h : ℚ) - (i : ℚ)| = ∑ i ∈ range h, ((h : ℚ) - (i : ℚ)) := by
    refine Finset.sum_congr rfl fun i hi => abs_of_nonneg ?_
    have : (i : ℚ) ≤ h := by exact_mod_cast (Finset.mem_range.mp hi).le
    linarith
  have e2 : ∑ j ∈ range (h + 1), |(h : ℚ) - ((h + j : ℕ) : ℚ)| = ∑ j ∈ range (h + 1), ((j : ℚ) + 0) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rw [show (h : ℚ) - (h + j) = -(j : ℚ) by ring, abs_neg, abs_of_nonneg (Nat.cast_nonneg j), add_zero]
  rw [e1, e2, sum_lin, sum_half]
  push_cast
  ring

lemma sum_abs_even (h : ℕ) :
    ∑ i ∈ range (2 * h), |((h : ℚ) - 1 / 2) - (i : ℚ)| = (h : ℚ) ^ 2 := by
  rw [show 2 * h = h + h by ring, Finset.sum_range_add]
  have e1 : ∑ i ∈ range h, |((h : ℚ) - 1 / 2) - (i : ℚ)| = ∑ i ∈ range h, (((h : ℚ) - 1 / 2) - (i : ℚ)) := by
    refine Finset.sum_congr rfl fun i hi => abs_of_nonneg ?_
    have : (i : ℚ) + 1 ≤ h := by exact_mod_cast (Finset.mem_range.mp hi)
    linarith
  have e2 : ∑ j ∈ range h, |((h : ℚ) - 1 / 2) - ((h + j : ℕ) : ℚ)| = ∑ j ∈ range h, ((j : ℚ) + 1 / 2) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rw [show (h : ℚ) - 1 / 2 - (h + j) = -((j : ℚ) + 1 / 2) by ring, abs_neg]
    exact abs_of_nonneg (by positivity)
  rw [e1, e2, sum_lin, sum_half]
  ring

/-- The function u(i) = |(n+1)/2 - (i+1)|. -/
def u (n : ℕ) (i : Fin n) : ℚ := |((n : ℚ) + 1) / 2 - ((i : ℕ) + 1)|

lemma u_sums (n : ℕ) :
    (n : ℚ) * ∑ i : Fin n, u n i ^ 2 - (∑ i : Fin n, u n i) ^ 2 = a n := by
  have hs2 : ∑ i : Fin n, u n i ^ 2 = ∑ i ∈ range n, (((n : ℚ) - 1) / 2 - (i : ℚ)) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (((n : ℚ) - 1) / 2 - (i : ℚ)) ^ 2) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold u
    rw [sq_abs]
    ring
  have hs1 : ∑ i : Fin n, u n i = ∑ i ∈ range n, |((n : ℚ) - 1) / 2 - (i : ℚ)| := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => |((n : ℚ) - 1) / 2 - (i : ℚ)|) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold u
    congr 1
    ring
  rw [hs1, hs2, sum_sq]
  unfold a
  rcases Nat.even_or_odd' n with ⟨h, rfl | rfl⟩
  · have e : ((2 * h : ℕ) : ℚ) - 1 = 2 * ((h : ℚ) - 1 / 2) := by push_cast; ring
    rw [e, mul_div_cancel_left₀ _ (by norm_num : (2 : ℚ) ≠ 0), sum_abs_even,
      (even_two_mul h).neg_one_pow]
    push_cast
    ring
  · have e : ((2 * h + 1 : ℕ) : ℚ) - 1 = 2 * (h : ℚ) := by push_cast; ring
    rw [e, mul_div_cancel_left₀ _ (by norm_num : (2 : ℚ) ≠ 0), sum_abs_odd,
      (odd_two_mul_add_one h).neg_one_pow]
    push_cast
    ring

/-- The quantity `(Σ v)^2 - n Σ v^2` for `v = c + e u` with `e^2 = 1`. -/
lemma shift (n : ℕ) (c e : ℚ) (he : e ^ 2 = 1) :
    (∑ i : Fin n, (c + e * u n i)) ^ 2 - (n : ℚ) * ∑ i : Fin n, (c + e * u n i) ^ 2
      = -((n : ℚ) * ∑ i : Fin n, u n i ^ 2 - (∑ i : Fin n, u n i) ^ 2) := by
  have h1 : ∑ i : Fin n, (c + e * u n i) = n * c + e * ∑ i : Fin n, u n i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum]
  have h2 : ∑ i : Fin n, (c + e * u n i) ^ 2
      = n * c ^ 2 + 2 * c * e * ∑ i : Fin n, u n i + e ^ 2 * ∑ i : Fin n, u n i ^ 2 := by
    have : ∀ i : Fin n, (c + e * u n i) ^ 2 = c ^ 2 + 2 * c * e * u n i + e ^ 2 * u n i ^ 2 := by
      intro i; ring
    simp only [this]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [h1, h2]
  linear_combination ((∑ i : Fin n, u n i) ^ 2 - (n : ℚ) * ∑ i : Fin n, u n i ^ 2) * he

lemma a_nonneg (n : ℕ) : 0 ≤ a n := by
  rw [← u_sums n]
  have hcs : (∑ i : Fin n, u n i * 1) ^ 2 ≤ (∑ i : Fin n, u n i ^ 2) * ∑ i : Fin n, (1 : ℚ) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => u n i) (fun _ => 1)
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    at hcs
  linarith

theorem result (n : ℕ) (hn : 1 < n) :
    (|(A n).charpoly.coeff (n - 2)| = a n ∧ ∀ k : ℕ, 2 < k → k ≤ n → (A n).charpoly.coeff (n - k) = 0) ∧
    (|(B n).charpoly.coeff (n - 2)| = a n ∧ ∀ k : ℕ, 2 < k → k ≤ n → (B n).charpoly.coeff (n - k) = 0) := by
  have hA : A n = Mv (fun i => (n : ℚ) / 2 + (-1) * u n i) := by
    ext i j
    simp only [A, Mv, u, Matrix.of_apply]
    ring
  have hB : B n = Mv (fun i => ((n % 2 : ℕ) : ℚ) / 2 + 1 * u n i) := by
    ext i j
    simp only [B, Mv, u, Matrix.of_apply]
    ring
  have hpos := a_nonneg n
  constructor
  · rw [hA]
    obtain ⟨h1, h2⟩ := coeff_Mv (by omega : 2 ≤ n) (fun i => (n : ℚ) / 2 + (-1) * u n i)
    refine ⟨?_, h2⟩
    rw [h1, shift n _ (-1) (by norm_num), u_sums, abs_neg, abs_of_nonneg hpos]
  · rw [hB]
    obtain ⟨h1, h2⟩ := coeff_Mv (by omega : 2 ≤ n) (fun i => ((n % 2 : ℕ) : ℚ) / 2 + 1 * u n i)
    refine ⟨?_, h2⟩
    rw [h1, shift n _ 1 (by norm_num), u_sums, abs_neg, abs_of_nonneg hpos]

end OMA.A350050

theorem OMA.solution : type_of% @OMA.S_oeis_a350050.main :=
  fun n hn => OMA.A350050.result n hn

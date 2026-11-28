import OMAStatements.S_oeis_a338198
import Mathlib

open OMA.S_oeis_a338198

private lemma Hsum (k r : ℕ) (x : ℚ) (hx : x = -2 ∨ x = 1) :
    ∑ i ∈ Finset.range (r + 1), (((k + i : ℕ) : ℚ) ^ 2 - 2) * x ^ i / ((k + i).factorial : ℚ) =
      -(((k + r + 1 : ℕ) : ℚ) * (((k + r + 1 : ℕ) : ℚ) + x) * x ^ (r + 1) / ((k + r + 1).factorial : ℚ))
      + (k : ℚ) * ((k : ℚ) + x) / (k.factorial : ℚ) := by
  induction r with
  | zero =>
    rw [Finset.sum_range_one]
    simp only [add_zero, pow_zero, mul_one, zero_add, pow_one]
    rw [Nat.factorial_succ]
    push_cast
    have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((k : ℚ) + 1) ≠ 0 := by positivity
    rcases hx with rfl | rfl
    · field_simp; ring
    · field_simp; ring
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show k + (r + 1) = k + r + 1 by ring]
    rw [Nat.factorial_succ (k + r + 1)]
    push_cast
    have h1 : ((k + r + 1).factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((k : ℚ) + r + 1 + 1) ≠ 0 := by positivity
    rcases hx with rfl | rfl
    · field_simp; ring
    · field_simp; ring

private lemma T_eq (n k : ℕ) (h : k ≤ n) :
    T n k = (((k : ℚ) + 1) * 2 ^ (n - k) - ((k : ℚ) - 2) * (-1) ^ (n - k)) / 3 := by
  unfold T; rw [if_pos h]

private lemma T_zero (n k : ℕ) (h : n < k) : T n k = 0 := by unfold T; rw [if_neg (by omega)]

private lemma M_zero (n k : ℕ) (h : n < k) : M n k = 0 := by unfold M; rw [if_pos h]

private lemma M_diag (n : ℕ) : M n n = 1 := by unfold M; simp

private lemma M_sub (n : ℕ) : M (n + 1) n = 1 - ((n : ℚ) + 1) := by
  unfold M; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]; push_cast; ring

private lemma M_gen (n k : ℕ) (h : k + 2 ≤ n) :
    M n k = (-1) ^ (n - k) * ((k : ℚ) ^ 2 - 2) * ((n - 2).factorial : ℚ) / (k.factorial : ℚ) := by
  unfold M; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private lemma prodMT (n k : ℕ) : (∑ j ∈ Finset.range (n + 1), M n j * T j k) = (if n = k then 1 else 0) := by
  rcases Nat.lt_or_ge n k with h | h
  · rw [if_neg (by omega)]
    apply Finset.sum_eq_zero; intro j hj; simp at hj
    rw [T_zero j k (by omega)]; ring
  obtain ⟨d, rfl⟩ : ∃ d, n = k + d := ⟨n - k, by omega⟩
  rw [show k + d + 1 = k + (d + 1) by ring, Finset.sum_range_add,
    Finset.sum_eq_zero (fun j hj => by simp at hj; rw [T_zero j k (by omega)]; ring), zero_add]
  rcases d with _ | _ | r
  · rw [Finset.sum_range_one]
    simp only [add_zero]
    rw [M_diag, T_eq k k le_rfl, Nat.sub_self]
    simp
    ring
  · rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [add_zero, zero_add]
    rw [M_sub, M_diag, T_eq k k le_rfl, T_eq (k + 1) k (by omega), Nat.sub_self,
      show k + 1 - k = 1 by omega]
    rw [if_neg (by omega)]
    ring
  · rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hgen : ∀ i ∈ Finset.range (r + 1), M (k + (r + 1 + 1)) (k + i) * T (k + i) k =
        ((k + r).factorial : ℚ) * (-1) ^ r / 3 * ((((k + i : ℕ) : ℚ) ^ 2 - 2) *
          (((k : ℚ) + 1) * (-2) ^ i - ((k : ℚ) - 2)) / ((k + i).factorial : ℚ)) := by
      intro i hi
      simp at hi
      rw [M_gen _ _ (by omega), T_eq (k + i) k (by omega),
        show k + i - k = i by omega, show k + (r + 1 + 1) - 2 = k + r by omega,
        show k + (r + 1 + 1) - (k + i) = (r - i) + 2 by omega]
      have hs : (-1 : ℚ) ^ (r - i) = (-1) ^ r * (-1) ^ i := by
        have h3 : (-1 : ℚ) ^ (r - i) * (-1) ^ i = (-1) ^ r := by
          rw [← pow_add, show r - i + i = r by omega]
        have h4 : ((-1 : ℚ) ^ i) * ((-1) ^ i) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
        calc (-1 : ℚ) ^ (r - i) = (-1) ^ (r - i) * ((-1) ^ i * (-1) ^ i) := by rw [h4, mul_one]
          _ = (-1) ^ r * (-1) ^ i := by rw [← mul_assoc, h3]
      have hii : ((-1 : ℚ) ^ i) * ((-1) ^ i) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
      rw [pow_add, hs, show ((-2 : ℚ)) ^ i = (-1) ^ i * 2 ^ i by rw [← mul_pow]; norm_num]
      push_cast
      linear_combination (-((-1 : ℚ) ^ r * ((k + r).factorial : ℚ) / (3 * ((k + i).factorial : ℚ)) *
        (((k : ℚ) + i) ^ 2 - 2) * ((k : ℚ) - 2))) * hii
    rw [Finset.sum_congr rfl hgen, ← Finset.mul_sum]
    have h1 := Hsum k r (-2) (Or.inl rfl)
    have h2 := Hsum k r 1 (Or.inr rfl)
    have hsplit : ∑ i ∈ Finset.range (r + 1), (((k + i : ℕ) : ℚ) ^ 2 - 2) *
        (((k : ℚ) + 1) * (-2) ^ i - ((k : ℚ) - 2)) / ((k + i).factorial : ℚ) =
        ((k : ℚ) + 1) * ∑ i ∈ Finset.range (r + 1), (((k + i : ℕ) : ℚ) ^ 2 - 2) * (-2) ^ i / ((k + i).factorial : ℚ)
        - ((k : ℚ) - 2) * ∑ i ∈ Finset.range (r + 1), (((k + i : ℕ) : ℚ) ^ 2 - 2) * 1 ^ i / ((k + i).factorial : ℚ) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hsplit, h1, h2]
    rw [show k + (r + 1 + 1) = (k + (r + 1)) + 1 by ring, M_sub, M_diag,
      T_eq _ _ (by omega), T_eq _ _ (by omega), show k + (r + 1) - k = r + 1 by omega,
      show k + (r + 1) + 1 - k = r + 2 by omega, if_neg (by omega)]
    rw [show k + (r + 1) = k + r + 1 by ring, Nat.factorial_succ (k + r)]
    push_cast
    have : ((k + r).factorial : ℚ) ≠ 0 := by positivity
    have : (k.factorial : ℚ) ≠ 0 := by positivity
    have : ((k : ℚ) + r + 1) ≠ 0 := by positivity
    rw [pow_succ (-2 : ℚ) r, pow_succ (-1 : ℚ) r, pow_succ (2 : ℚ) r, pow_succ (2 : ℚ) (r + 1),
      pow_succ (-1 : ℚ) (r + 1), pow_succ (2 : ℚ) r]
    rcases Nat.even_or_odd r with he | ho
    · simp only [pow_succ, he.neg_one_pow, he.neg_pow]
      field_simp
      ring
    · simp only [pow_succ, ho.neg_one_pow, ho.neg_pow]
      field_simp
      ring

private lemma prodTM (n k : ℕ) : (∑ j ∈ Finset.range (n + 1), T n j * M j k) = (if n = k then 1 else 0) := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := fun i j => M i j
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := fun i j => T i j
  have hAB : A * B = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h1 : ∑ l : Fin (n + 1), A i l * B l j = ∑ l ∈ Finset.range (n + 1), M i l * T l j :=
      Fin.sum_univ_eq_sum_range (fun l => M i l * T l j) (n + 1)
    rw [h1]
    have h2 : ∑ l ∈ Finset.range (n + 1), M i l * T l j = ∑ l ∈ Finset.range (i + 1), M i l * T l j := by
      have hi : (i : ℕ) + 1 ≤ n + 1 := by omega
      rw [← Finset.sum_range_add_sum_Ico _ hi]
      rw [Finset.sum_eq_zero (s := Finset.Ico _ _) (fun l hl => by
        simp at hl; rw [M_zero i l (by omega)]; ring), add_zero]
    rw [h2, prodMT]
    simp [Fin.ext_iff]
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_card_eq (Fin (n + 1)) (Fin (n + 1)) ℚ rfl).mp hAB
  rcases Nat.lt_or_ge n k with h | h
  · rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro j hj; simp at hj
    rw [M_zero j k (by omega)]; ring
  · have := congrFun (congrFun hBA ⟨n, by omega⟩) ⟨k, by omega⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    have h1 : ∑ l : Fin (n + 1), B ⟨n, by omega⟩ l * A l ⟨k, by omega⟩ =
        ∑ l ∈ Finset.range (n + 1), T n l * M l k :=
      Fin.sum_univ_eq_sum_range (fun l => T n l * M l k) (n + 1)
    rw [h1] at this
    rw [this]
    simp [Fin.ext_iff]

theorem OMA.solution : type_of% @OMA.S_oeis_a338198.main := fun n k => ⟨prodTM n k, prodMT n k⟩

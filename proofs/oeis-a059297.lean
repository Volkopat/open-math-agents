import OMAStatements.S_oeis_a059297

/-!
# Proof of Mathar's conjecture on A059297: its matrix inverse is A137452

For `k ≥ 1` and `n = k + m`, the entry `(n, k)` of `A059297 * A137452` is, after putting
`j = k + i`, equal to `k * C(n, k) * Σ_{i ≤ m} (-1)^i C(m, i) (k + i)^(m - 1)`, the `m`-th forward
difference of `x ↦ x^(m - 1)` up to sign, hence `0` for `m ≥ 1` and `1` for `m = 0`.
The other product follows since a one-sided inverse of a square matrix is two-sided.
-/

namespace OMA.S_oeis_a059297.Proof

open OMA.S_oeis_a059297 Polynomial

open Finset

lemma B_zero_right (j : ℕ) : A137452 j 0 = if j = 0 then 1 else 0 := by
  unfold A137452
  by_cases h : j = 0 <;> simp [h]

lemma B_succ (j k : ℕ) (hj : j ≠ 0) :
    A137452 j (k + 1) = (-(j : ℤ)) ^ (j - 1 - k) * ((j - 1).choose k : ℤ) := by
  unfold A137452
  rw [if_neg hj, coeff_X_mul, sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow]

lemma B_zero_left (k : ℕ) (hk : k ≠ 0) : A137452 0 k = 0 := by
  simp [A137452, hk]

/-- The key finite-difference identity. -/
lemma alt_sum_eq_zero (k m : ℕ) (hm : 1 ≤ m) :
    ∑ i ∈ range (m + 1), (-1 : ℤ) ^ i * (m.choose i : ℤ) * ((k : ℤ) + i) ^ (m - 1) = 0 := by
  have h := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ) (j := m - 1) (n := m) (by omega))
    (k : ℤ)
  rw [fwdDiff_iter_eq_sum_shift] at h
  simp only [Pi.zero_apply, smul_eq_mul, nsmul_eq_mul, mul_one] at h
  have : ∑ i ∈ range (m + 1), (-1 : ℤ) ^ i * (m.choose i : ℤ) * ((k : ℤ) + i) ^ (m - 1) =
      (-1) ^ m * ∑ i ∈ range (m + 1),
        (-1 : ℤ) ^ (m - i) * (m.choose i : ℤ) * ((k : ℤ) + i) ^ (m - 1) := by
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have : (-1 : ℤ) ^ i = (-1) ^ m * (-1) ^ (m - i) := by
      rw [← pow_add, show m + (m - i) = i + 2 * (m - i) by omega, pow_add, pow_mul]; simp
    rw [this]; ring
  rw [this, h, mul_zero]

lemma nat_id (k i m : ℕ) (hi : i ≤ m) :
    (k + 1 + m).choose (k + 1 + i) * ((k + 1 + i) * (k + i).choose k) =
      (k + 1 + m).choose (k + 1) * m.choose i * (k + 1) := by
  have h1 : (k + 1 + i) * (k + i).choose k = (k + 1 + i).choose (k + 1) * (k + 1) := by
    have := Nat.add_one_mul_choose_eq (k + i) k
    rw [show k + 1 + i = k + i + 1 by omega]; exact this
  rw [h1, ← mul_assoc, Nat.choose_mul (by omega : k + 1 ≤ k + 1 + i)]
  rw [show k + 1 + m - (k + 1) = m by omega, show k + 1 + i - (k + 1) = i by omega]

lemma term_eq (k i m : ℕ) (hi : i ≤ m) (hm : 1 ≤ m) :
    ((k + 1 + m).choose (k + 1 + i) : ℤ) * ((k + 1 + i : ℕ) : ℤ) ^ (k + 1 + m - (k + 1 + i)) *
      ((-((k + 1 + i : ℕ) : ℤ)) ^ (k + 1 + i - 1 - k) * ((k + 1 + i - 1).choose k : ℤ)) =
    ((k + 1 : ℕ) : ℤ) * ((k + 1 + m).choose (k + 1) : ℤ) *
      ((-1 : ℤ) ^ i * (m.choose i : ℤ) * (((k + 1 : ℕ) : ℤ) + i) ^ (m - 1)) := by
  rw [show k + 1 + m - (k + 1 + i) = m - i by omega, show k + 1 + i - 1 - k = i by omega,
    show k + 1 + i - 1 = k + i by omega]
  have hn := congrArg (fun x : ℕ => (x : ℤ)) (nat_id k i m hi)
  push_cast at hn
  have hp : ((k : ℤ) + 1 + i) ^ (m - i) * ((k : ℤ) + 1 + i) ^ i =
      ((k : ℤ) + 1 + i) * ((k : ℤ) + 1 + i) ^ (m - 1) := by
    rw [← pow_add, ← pow_succ', show m - i + i = m - 1 + 1 by omega]
  push_cast
  rw [neg_pow]
  linear_combination ((-1 : ℤ) ^ i * ((k : ℤ) + 1 + i) ^ (m - 1)) * hn +
    ((-1 : ℤ) ^ i * ((k + 1 + m).choose (k + 1 + i) : ℤ) * ((k + i).choose k : ℤ)) * hp

lemma prod_eq (n K : ℕ) :
    ∑ j ∈ range (n + 1), A059297 n j * A137452 j K = if n = K then 1 else 0 := by
  rcases K with _ | k
  · rw [sum_eq_single 0]
    · simp [A059297, B_zero_right]
      rcases n with _ | n <;> simp
    · intro j _ hj; rw [B_zero_right, if_neg hj, mul_zero]
    · intro h; simp at h
  · -- terms with `j ≤ k` vanish
    have hsmall : ∀ j, j ≤ k → A137452 j (k + 1) = 0 := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact B_zero_left _ (by omega)
      · rw [B_succ j k (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp
    by_cases hn : n < k + 1
    · rw [if_neg (by omega)]
      exact sum_eq_zero fun j hj => by
        rw [hsmall j (by have := mem_range.mp hj; omega), mul_zero]
    obtain ⟨m, rfl⟩ : ∃ m, n = k + 1 + m := ⟨n - (k + 1), by omega⟩
    rw [← sum_range_add_sum_Ico _ (show k + 1 ≤ k + 1 + m + 1 by omega)]
    rw [sum_eq_zero (fun j hj => by rw [hsmall j (by have := mem_range.mp hj; omega), mul_zero]),
      zero_add, sum_Ico_eq_sum_range, show k + 1 + m + 1 - (k + 1) = m + 1 by omega]
    have hterm : ∀ i ∈ range (m + 1), A059297 (k + 1 + m) (k + 1 + i) * A137452 (k + 1 + i) (k + 1)
        = ((k + 1 + m).choose (k + 1 + i) : ℤ) * ((k + 1 + i : ℕ) : ℤ) ^ (k + 1 + m - (k + 1 + i)) *
          ((-((k + 1 + i : ℕ) : ℤ)) ^ (k + 1 + i - 1 - k) * ((k + 1 + i - 1).choose k : ℤ)) := by
      intro i _
      rw [B_succ _ _ (by omega)]; rfl
    rw [sum_congr rfl hterm]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [if_neg (by omega),
        sum_congr rfl fun i hi => term_eq k i m (Nat.lt_succ_iff.mp (mem_range.mp hi)) hm,
        ← mul_sum]
      have := alt_sum_eq_zero (k + 1) m hm
      push_cast at this ⊢
      rw [this, mul_zero]

lemma block_mul (N : ℕ) : block A059297 N * block A137452 N = 1 := by
  ext i l
  simp only [block, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Fin.sum_univ_eq_sum_range (fun j => A059297 i j * A137452 j l) N]
  rw [← sum_subset (show range (i + 1) ⊆ range N from by
      intro j hj; simp only [mem_range] at hj ⊢; omega)]
  · rw [prod_eq]; exact if_congr Fin.val_inj rfl rfl
  · intro j _ hj
    simp only [mem_range, not_lt] at hj
    simp [A059297, Nat.choose_eq_zero_of_lt (show (i : ℕ) < j by omega)]

end OMA.S_oeis_a059297.Proof

open OMA.S_oeis_a059297 OMA.S_oeis_a059297.Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a059297.main :=
  fun N => ⟨block_mul N, mul_eq_one_comm.mp (block_mul N)⟩

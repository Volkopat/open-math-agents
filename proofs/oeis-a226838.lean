import OMAStatements.S_oeis_a226838

namespace R226838
open OMA.S_oeis_a226838

theorem a_zero : a 0 = 1 := by
  rw [a]

/-- The multiples `c + 1, 2 (c + 1), ..., j (c + 1)` give `(c + 1)^j * j! ∣ (j (c + 1))!`. -/
theorem pow_fact_dvd (c j : ℕ) : (c + 1) ^ j * j.factorial ∣ (j * (c + 1)).factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e1 : ((j + 1) * (c + 1)).factorial =
        (j * (c + 1) + c + 1) * (j * (c + 1) + c).factorial := by
      rw [show (j + 1) * (c + 1) = j * (c + 1) + c + 1 by ring]
      exact Nat.factorial_succ _
    have e2 : (c + 1) ^ (j + 1) * (j + 1).factorial =
        (j * (c + 1) + c + 1) * ((c + 1) ^ j * j.factorial) := by
      rw [Nat.factorial_succ, pow_succ]
      ring
    rw [e1, e2]
    exact Nat.mul_dvd_mul_left _ (ih.trans (Nat.factorial_dvd_factorial (Nat.le_add_right _ _)))

/-- With `K = m + 2`: `K^m * K! ∣ (K^2 - 1)!`. -/
theorem pow_fact_dvd2 (m : ℕ) :
    (m + 1 + 1) ^ m * (m + 1 + 1).factorial ∣ ((m + 1 + 1) ^ 2 - 1).factorial := by
  have h1 := pow_fact_dvd (m + 1) (m + 1)
  have e : (m + 1 + 1) ^ (m + 1) * (m + 1).factorial =
      (m + 1 + 1) ^ m * (m + 1 + 1).factorial := by
    rw [Nat.factorial_succ (m + 1), pow_succ]
    ring
  rw [e] at h1
  refine h1.trans (Nat.factorial_dvd_factorial ?_)
  have : (m + 1) * (m + 1 + 1) + (m + 1) + 1 = (m + 1 + 1) ^ 2 := by ring
  omega

theorem six_pow_dvd (m : ℕ) : (m + 1 + 1) ^ m * 6 ∣ ((m + 1 + 1) ^ 2 - 1).factorial := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · first
      | (norm_num [Nat.factorial]; done)
      | decide
  · have h3 : (3 : ℕ).factorial ∣ (m + 1 + 1).factorial :=
      Nat.factorial_dvd_factorial (by omega)
    have h6 : (3 : ℕ).factorial = 6 := by decide
    rw [h6] at h3
    exact (Nat.mul_dvd_mul_left _ h3).trans (pow_fact_dvd2 m)

/-- If `K^m * M ∣ (K^2 - 1)!` (with `K = m + 2`), then `M` divides the coefficient.
The exponent `e` is `K - 2 = m`, in whatever form `simp` left it. -/
theorem coef_dvd {n m M e : ℕ} (he : e = m) (h : (m + 1 + 1) ^ 2 ≤ n + 1)
    (hM : (m + 1 + 1) ^ m * M ∣ ((m + 1 + 1) ^ 2 - 1).factorial) :
    M ∣ n.factorial / ((n + 1 - (m + 1 + 1) ^ 2).factorial * (m + 1 + 1) ^ e) := by
  rw [he]
  have hs : 0 < (m + 1 + 1) ^ 2 := by positivity
  have hf := Nat.factorial_mul_descFactorial (show (m + 1 + 1) ^ 2 - 1 ≤ n by omega)
  rw [show n - ((m + 1 + 1) ^ 2 - 1) = n + 1 - (m + 1 + 1) ^ 2 by omega] at hf
  apply Nat.dvd_div_of_mul_dvd
  rw [← hf, mul_assoc]
  exact Nat.mul_dvd_mul_left _ (hM.trans (Nat.factorial_dvd_descFactorial _ _))

theorem aux {x y S : ℕ} (hx : x = y) (hS : 6 ∣ S) : x + S ≡ y [MOD 6] := by
  obtain ⟨c, rfl⟩ := hS
  subst hx
  unfold Nat.ModEq
  omega

theorem step (n : ℕ) : a (n + 1) ≡ a n [MOD 6] := by
  rw [a, Fin.sum_univ_succ]
  apply aux
  · simp [Nat.div_self (Nat.factorial_pos n)]
  · apply Finset.dvd_sum
    intro i _
    simp only [Fin.val_succ]
    split_ifs with h
    · apply Dvd.dvd.mul_right
      exact coef_dvd (by omega) h (six_pow_dvd i.1)
    · exact dvd_zero 6

end R226838

theorem OMA.solution : type_of% @OMA.S_oeis_a226838.main := by
  intro n
  induction n with
  | zero =>
    unfold Nat.ModEq
    rw [R226838.a_zero]
  | succ n ih => exact (R226838.step n).trans ih

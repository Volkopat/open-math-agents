import OMAStatements.S_oeis_a387064

/-! Following @Git-Tim1 (#11179), retain the row separation and totient count.
Use Mathlib's binomial factorization bound and prime-power identity in place
of the custom carry-count arguments. -/

open Finset

theorem OMA.solution : type_of% @OMA.S_oeis_a387064.main := by
  intro p k hp hk
  have : Fact p.Prime := ⟨hp⟩
  have early {r j : ℕ} (hr : r < p ^ k) (hj : j ≤ r) : ¬ p ^ k ∣ r.choose j := by
    rw [hp.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hj)]
    exact not_le.mpr (Nat.factorization_choose_le_log.trans_lt
      (Nat.log_lt_of_lt_pow' (by omega : k ≠ 0) hr))
  have lastRow {j : ℕ} (hj : j ≤ p ^ k) : p ^ k ∣ (p ^ k).choose j ↔ ¬ p ∣ j := by
    by_cases hj0 : j = 0
    · subst j
      simp only [Nat.choose_zero_right, dvd_zero, not_true_eq_false, iff_false]
      intro h
      have := Nat.le_of_dvd (by norm_num : 0 < 1) h
      have : p ≤ p ^ k := by simpa using Nat.pow_le_pow_right hp.pos hk
      have := hp.two_le
      omega
    · rw [hp.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hj),
        hp.dvd_iff_one_le_factorization hj0]
      have := Nat.factorization_choose_prime_pow_add_factorization hp hj hj0
      omega
  unfold OMA.S_oeis_a387064.a
  rw [sum_range_succ]
  have lower : ∀ r ∈ range (p ^ k),
      ((range (r + 1)).filter fun j => p ^ k ∣ r.choose j).card = 0 := by
    intro r hr
    apply card_eq_zero.mpr
    apply filter_eq_empty_iff.mpr
    intro j hj
    exact early (mem_range.mp hr) (by simpa using mem_range.mp hj)
  rw [sum_eq_zero lower, zero_add]
  have hset : ((range (p ^ k + 1)).filter fun j => p ^ k ∣ (p ^ k).choose j) =
      ((range (p ^ k)).filter fun j => (p ^ k).Coprime j) := by
    ext j
    simp only [mem_filter, mem_range, Nat.lt_succ_iff, Nat.coprime_pow_left_iff hk,
      hp.coprime_iff_not_dvd]
    constructor
    · rintro ⟨hj, hd⟩
      have h := (lastRow hj).mp hd
      refine ⟨lt_of_le_of_ne hj ?_, h⟩
      rintro rfl
      exact h (dvd_pow_self p (by omega))
    · rintro ⟨hj, h⟩
      exact ⟨hj.le, (lastRow hj.le).mpr h⟩
  rw [hset, ← Nat.totient, Nat.totient_prime_pow hp hk, mul_comm]

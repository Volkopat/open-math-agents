import OMAReductions.R_oeis_a070542_R1
import Mathlib

-- Step oeis-a070542.R1.H1: hypothesis H1 of reduction oeis-a070542.R1
-- Credit: @ivillar. Finite check: for each listed n, compute binomial(2n, n) via factorials, then interval_cases over p <= 2n with q = 2n - p and norm_num refutes primality, distinctness or divisibility.

/-! Step oeis-a070542.R1.H1. -/

namespace P8A070542

lemma case_1 : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.choose (2 * 1) 1 ∧
    q ∣ Nat.choose (2 * 1) 1 ∧ p + q = 2 * 1 := by
  rintro ⟨p, q, hp, hq, hne, hpd, hqd, hsum⟩
  have hC : Nat.choose (2 * 1) 1 = 2 := by
    rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
    norm_num [Nat.factorial]
  rw [hC] at hpd hqd
  obtain rfl : q = 2 * 1 - p := by omega
  have hp' : p ≤ 2 * 1 := by omega
  interval_cases p <;> first | (norm_num at hp; done) | (norm_num at hq; done) | (norm_num at hne; done) | (norm_num at hpd; done) | (norm_num at hqd; done)

lemma case_2 : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.choose (2 * 2) 2 ∧
    q ∣ Nat.choose (2 * 2) 2 ∧ p + q = 2 * 2 := by
  rintro ⟨p, q, hp, hq, hne, hpd, hqd, hsum⟩
  have hC : Nat.choose (2 * 2) 2 = 6 := by
    rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
    norm_num [Nat.factorial]
  rw [hC] at hpd hqd
  obtain rfl : q = 2 * 2 - p := by omega
  have hp' : p ≤ 2 * 2 := by omega
  interval_cases p <;> first | (norm_num at hp; done) | (norm_num at hq; done) | (norm_num at hne; done) | (norm_num at hpd; done) | (norm_num at hqd; done)

lemma case_3 : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.choose (2 * 3) 3 ∧
    q ∣ Nat.choose (2 * 3) 3 ∧ p + q = 2 * 3 := by
  rintro ⟨p, q, hp, hq, hne, hpd, hqd, hsum⟩
  have hC : Nat.choose (2 * 3) 3 = 20 := by
    rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
    norm_num [Nat.factorial]
  rw [hC] at hpd hqd
  obtain rfl : q = 2 * 3 - p := by omega
  have hp' : p ≤ 2 * 3 := by omega
  interval_cases p <;> first | (norm_num at hp; done) | (norm_num at hq; done) | (norm_num at hne; done) | (norm_num at hpd; done) | (norm_num at hqd; done)

lemma case_4 : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.choose (2 * 4) 4 ∧
    q ∣ Nat.choose (2 * 4) 4 ∧ p + q = 2 * 4 := by
  rintro ⟨p, q, hp, hq, hne, hpd, hqd, hsum⟩
  have hC : Nat.choose (2 * 4) 4 = 70 := by
    rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
    norm_num [Nat.factorial]
  rw [hC] at hpd hqd
  obtain rfl : q = 2 * 4 - p := by omega
  have hp' : p ≤ 2 * 4 := by omega
  interval_cases p <;> first | (norm_num at hp; done) | (norm_num at hq; done) | (norm_num at hne; done) | (norm_num at hpd; done) | (norm_num at hqd; done)

lemma case_6 : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.choose (2 * 6) 6 ∧
    q ∣ Nat.choose (2 * 6) 6 ∧ p + q = 2 * 6 := by
  rintro ⟨p, q, hp, hq, hne, hpd, hqd, hsum⟩
  have hC : Nat.choose (2 * 6) 6 = 924 := by
    rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
    norm_num [Nat.factorial]
  rw [hC] at hpd hqd
  obtain rfl : q = 2 * 6 - p := by omega
  have hp' : p ≤ 2 * 6 := by omega
  interval_cases p <;> first | (norm_num at hp; done) | (norm_num at hq; done) | (norm_num at hne; done) | (norm_num at hpd; done) | (norm_num at hqd; done)

lemma case_10 : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.choose (2 * 10) 10 ∧
    q ∣ Nat.choose (2 * 10) 10 ∧ p + q = 2 * 10 := by
  rintro ⟨p, q, hp, hq, hne, hpd, hqd, hsum⟩
  have hC : Nat.choose (2 * 10) 10 = 184756 := by
    rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
    norm_num [Nat.factorial]
  rw [hC] at hpd hqd
  obtain rfl : q = 2 * 10 - p := by omega
  have hp' : p ≤ 2 * 10 := by omega
  interval_cases p <;> first | (norm_num at hp; done) | (norm_num at hq; done) | (norm_num at hne; done) | (norm_num at hpd; done) | (norm_num at hqd; done)

lemma case_15 : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.choose (2 * 15) 15 ∧
    q ∣ Nat.choose (2 * 15) 15 ∧ p + q = 2 * 15 := by
  rintro ⟨p, q, hp, hq, hne, hpd, hqd, hsum⟩
  have hC : Nat.choose (2 * 15) 15 = 155117520 := by
    rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
    norm_num [Nat.factorial]
  rw [hC] at hpd hqd
  obtain rfl : q = 2 * 15 - p := by omega
  have hp' : p ≤ 2 * 15 := by omega
  interval_cases p <;> first | (norm_num at hp; done) | (norm_num at hq; done) | (norm_num at hne; done) | (norm_num at hpd; done) | (norm_num at hqd; done)

lemma case_26 : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.choose (2 * 26) 26 ∧
    q ∣ Nat.choose (2 * 26) 26 ∧ p + q = 2 * 26 := by
  rintro ⟨p, q, hp, hq, hne, hpd, hqd, hsum⟩
  have hC : Nat.choose (2 * 26) 26 = 495918532948104 := by
    rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
    norm_num [Nat.factorial]
  rw [hC] at hpd hqd
  obtain rfl : q = 2 * 26 - p := by omega
  have hp' : p ≤ 2 * 26 := by omega
  interval_cases p <;> first | (norm_num at hp; done) | (norm_num at hq; done) | (norm_num at hne; done) | (norm_num at hpd; done) | (norm_num at hqd; done)

lemma case_28 : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.choose (2 * 28) 28 ∧
    q ∣ Nat.choose (2 * 28) 28 ∧ p + q = 2 * 28 := by
  rintro ⟨p, q, hp, hq, hne, hpd, hqd, hsum⟩
  have hC : Nat.choose (2 * 28) 28 = 7648690600760440 := by
    rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
    norm_num [Nat.factorial]
  rw [hC] at hpd hqd
  obtain rfl : q = 2 * 28 - p := by omega
  have hp' : p ≤ 2 * 28 := by omega
  interval_cases p <;> first | (norm_num at hp; done) | (norm_num at hq; done) | (norm_num at hne; done) | (norm_num at hpd; done) | (norm_num at hqd; done)

lemma case_64 : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.choose (2 * 64) 64 ∧
    q ∣ Nat.choose (2 * 64) 64 ∧ p + q = 2 * 64 := by
  rintro ⟨p, q, hp, hq, hne, hpd, hqd, hsum⟩
  have hC : Nat.choose (2 * 64) 64 = 23951146041928082866135587776380551750 := by
    rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
    norm_num [Nat.factorial]
  rw [hC] at hpd hqd
  obtain rfl : q = 2 * 64 - p := by omega
  have hp' : p ≤ 2 * 64 := by omega
  interval_cases p <;> first | (norm_num at hp; done) | (norm_num at hq; done) | (norm_num at hne; done) | (norm_num at hpd; done) | (norm_num at hqd; done)

theorem a070542_h1 : ({1, 2, 3, 4, 6, 10, 15, 26, 28, 64} : Set ℕ) ⊆
    {n : ℕ | 1 ≤ n ∧ ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.choose (2 * n) n ∧
        q ∣ Nat.choose (2 * n) n ∧ p + q = 2 * n} := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, case_1⟩
  · exact ⟨by norm_num, case_2⟩
  · exact ⟨by norm_num, case_3⟩
  · exact ⟨by norm_num, case_4⟩
  · exact ⟨by norm_num, case_6⟩
  · exact ⟨by norm_num, case_10⟩
  · exact ⟨by norm_num, case_15⟩
  · exact ⟨by norm_num, case_26⟩
  · exact ⟨by norm_num, case_28⟩
  · exact ⟨by norm_num, case_64⟩

end P8A070542

theorem OMA.solution : OMA.R_oeis_a070542_R1.H1 :=
  P8A070542.a070542_h1

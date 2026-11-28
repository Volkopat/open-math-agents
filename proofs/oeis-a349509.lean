import OMAStatements.S_oeis_a349509
import Mathlib

-- Problem: A349509: a(n) is the denominator of binomial(n^3 + 6*n^2 - 6*n + 2, n^3 - 1)/n^3.
-- Upstream: formal-conjectures statements/oeis-a349509.lean:0 (declaration OMA.S_oeis_a349509.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write K = n^3, N = n^3 + 6 n^2 - 6 n + 2 and D = 2 n^2 - 2 n + 1, so N - (K - 1) = 3 D. The
absorption identity binomial(N, K) K = binomial(N, K - 1) (N - K + 1) shows that K divides
3 binomial(N, K - 1) D, and K is coprime to D because D = 1 + n (2 n - 2). Hence K divides
3 binomial(N, K - 1), the fraction is t / 3 for an integer t, and its denominator divides 3. -/

namespace A349509Aux

open OMA.S_oeis_a349509

theorem key (m : ℕ) :
    (m + 1) ^ 3 ∣ 3 * Nat.choose ((m + 1) ^ 3 + 6 * (m + 1) ^ 2 + 2 - 6 * (m + 1)) ((m + 1) ^ 3 - 1) := by
  obtain ⟨j, hj⟩ : ∃ j, (m + 1) ^ 3 = j + 1 := ⟨(m + 1) ^ 3 - 1, by
    have : 0 < (m + 1) ^ 3 := by positivity
    omega⟩
  have hN : (m + 1) ^ 3 + 6 * (m + 1) ^ 2 + 2 - 6 * (m + 1) = j + 3 * (2 * m ^ 2 + 2 * m + 1) := by
    have h1 : 6 * (m + 1) ^ 2 + 2 = 6 * (m + 1) + (3 * (2 * m ^ 2 + 2 * m + 1) - 1) := by
      have : 3 * (2 * m ^ 2 + 2 * m + 1) = 6 * m ^ 2 + 6 * m + 3 := by ring
      have h2 : 6 * (m + 1) ^ 2 + 2 = 6 * m ^ 2 + 12 * m + 8 := by ring
      omega
    have h3 : 1 ≤ 3 * (2 * m ^ 2 + 2 * m + 1) := by
      have : 3 * (2 * m ^ 2 + 2 * m + 1) = 6 * m ^ 2 + 6 * m + 3 := by ring
      omega
    omega
  have hj' : (m + 1) ^ 3 - 1 = j := by omega
  rw [hN, hj']
  have hid := Nat.choose_succ_right_eq (j + 3 * (2 * m ^ 2 + 2 * m + 1)) j
  rw [Nat.add_sub_cancel_left] at hid
  have hdvd : (m + 1) ^ 3 ∣
      3 * Nat.choose (j + 3 * (2 * m ^ 2 + 2 * m + 1)) j * (2 * m ^ 2 + 2 * m + 1) := by
    refine ⟨Nat.choose (j + 3 * (2 * m ^ 2 + 2 * m + 1)) (j + 1), ?_⟩
    rw [hj]
    have : 3 * Nat.choose (j + 3 * (2 * m ^ 2 + 2 * m + 1)) j * (2 * m ^ 2 + 2 * m + 1) =
        Nat.choose (j + 3 * (2 * m ^ 2 + 2 * m + 1)) j * (3 * (2 * m ^ 2 + 2 * m + 1)) := by ring
    rw [this, ← hid]
    ring
  have hc : Nat.Coprime (m + 1) (2 * m ^ 2 + 2 * m + 1) := by
    have h1 : 2 * m ^ 2 + 2 * m + 1 = 1 + (m + 1) * (2 * m) := by ring
    rw [h1]
    exact (Nat.coprime_add_mul_left_right (m + 1) 1 (2 * m)).mpr (Nat.coprime_one_right _)
  exact (Nat.Coprime.pow_left 3 hc).dvd_of_dvd_mul_right hdvd

theorem den_cases (n : ℕ) (hn : 1 ≤ n) : a n = 1 ∨ a n = 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨t, ht⟩ := key m
  unfold a
  set c : ℕ := Nat.choose ((m + 1) ^ 3 + 6 * (m + 1) ^ 2 + 2 - 6 * (m + 1)) ((m + 1) ^ 3 - 1) with hc
  have hK : ((m + 1 : ℕ) : ℚ) ^ 3 ≠ 0 := by positivity
  have hq : (c : ℚ) / ((m + 1 : ℕ) : ℚ) ^ 3 = ((t : ℤ) : ℚ) / ((3 : ℤ) : ℚ) := by
    have ht' : (3 : ℚ) * (c : ℚ) = ((m + 1 : ℕ) : ℚ) ^ 3 * (t : ℚ) := by exact_mod_cast ht
    rw [div_eq_div_iff hK (by norm_num)]
    push_cast
    push_cast at ht'
    linarith
  rw [hq]
  have hd : (((t : ℤ) : ℚ) / ((3 : ℤ) : ℚ)).den ∣ 3 := by
    have := Rat.den_dvd (t : ℤ) 3
    exact_mod_cast this
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact Or.inl h
  · exact Or.inr h

end A349509Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a349509.main :=
  A349509Aux.den_cases

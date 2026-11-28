import Mathlib

/-!
# A226115: Least positive integer not of the form p_m - p_{m-1} + ... +(-1)^(m-k)*p_k with 0 < k < m <= n, where p_j denotes the j-th prime.

Source: https://oeis.org/A226115
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A226115 (Zhi-Wei Sun, May 27 2013): sqrt(2*a(n)) >
sqrt(p_n)-0.7 for all n > 0, and a(n) is even for any n > 7.

Conventions:
* The sequence has offset 1 (data 1, 2, 3, 6, 7, 10, 11, 14, 18, 18, 20, 20, ...).
* p_k is the k-th prime with p_1 = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth Nat.Prime 0
  = 2`), p_k is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below is p_k.
* a(n) is the least positive integer v that is not of the form p_m - p_{m-1} + ... +
  (-1)^(m-k)*p_k with 0 < k < m <= n; the alternating sum is Sum_{j=k..m} (-1)^(m-j)*p_j, computed
  in `ℤ`. Such a v always exists, and a(n) is written as `sInf` of the set of positive integers
  that are not of this form.
* The inequality is stated in `ℝ` (sqrt is `Real.sqrt`, 0.7 is 7/10). Both assertions are
  formalized, as a conjunction.
-/

namespace OMA.S_oeis_a226115

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- A226115: the least positive integer not of the form p_m - p_{m-1} + ... + (-1)^(m-k) p_k with
0 < k < m <= n. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {v : ℕ | 0 < v ∧ ¬ ∃ k m : ℕ, 0 < k ∧ k < m ∧ m ≤ n ∧
    (v : ℤ) = ∑ j ∈ Finset.Icc k m, (-1) ^ (m - j) * (pr j : ℤ)}

/-- The conjecture recorded in A226115. -/
theorem main : (∀ n : ℕ, 0 < n → Real.sqrt (2 * (a n : ℝ)) > Real.sqrt (pr n) - 7 / 10) ∧
    (∀ n : ℕ, 7 < n → Even (a n)) := by
  sorry

end OMA.S_oeis_a226115

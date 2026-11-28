import Mathlib

/-!
# A248143: Least integer m > 0 such that m + n divides p(m) + p(n), where p(.) is the partition function given by A000041.

Source: https://oeis.org/A248143
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A248143 (Zhi-Wei Sun, Oct 02 2014): a(n) exists for any
n > 0.

Conventions:
* The sequence has offset 1 (data 1, 1, 1, 61, 13, 7, 1, 25, 109, 41, 60, 1, ...).
* p(.) is the partition function A000041: p(z) is the cardinality of the Mathlib type
  `Nat.Partition z` (helper `p`).
* `a(n) exists` means that there is a positive integer m with the stated divisibility (then the
  least such m exists); it is stated directly as the existence of m, without defining a(n).
-/

namespace OMA.S_oeis_a248143

/-- p(n), the number of partitions of n. -/
def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The conjecture recorded in A248143. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ p m + p n := by
  sorry

end OMA.S_oeis_a248143

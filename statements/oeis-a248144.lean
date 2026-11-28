import Mathlib

/-!
# A248144: Least positive integer m such that m + n divides p(m*n), where p(.) is the partition function given by A000041.

Source: https://oeis.org/A248144
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A248144 (Zhi-Wei Sun, Oct 02 2014): a(n) exists for any
n > 0.

Conventions:
* The sequence has offset 1 (data 4, 5, 3, 1, 2, 14, 2, 10, 1, 4, 17, 5, ...).
* p(.) is the partition function A000041: p(z) is the cardinality of the Mathlib type
  `Nat.Partition z` (helper `p`).
* `a(n) exists` means that there is a positive integer m with the stated divisibility (then the
  least such m exists); it is stated directly as the existence of m, without defining a(n).
-/

namespace OMA.S_oeis_a248144

/-- p(n), the number of partitions of n. -/
def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The conjecture recorded in A248144. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ p (m * n) := by
  sorry

end OMA.S_oeis_a248144

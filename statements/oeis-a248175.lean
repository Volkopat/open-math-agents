import Mathlib

/-!
# A248175: Least positive integer m such that m + n divides q(m*n), where q(.) is the strict partition function given by A000009.

Source: https://oeis.org/A248175
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A248175 (Zhi-Wei Sun, Oct 03 2014), part (i): a(n)
exists for any n > 0.

Conventions:
* The sequence has offset 1 (data 11, 4, 9, 2, 12, 10, 9, 16, 3, 6, 1, 5, ...).
* q(.) is the strict partition function A000009: q(m) is the number of partitions of m into
  distinct parts, the cardinality of the Mathlib finset `Nat.Partition.distincts m` (helper `q`).
* `a(n) exists` means that there is a positive integer m with the stated divisibility (then the
  least such m exists); it is stated directly as the existence of m, without defining a(n).
* Only part (i) of the conjecture is formalized; part (ii) is a different statement.
-/

namespace OMA.S_oeis_a248175

/-- q(m), the number of partitions of m into distinct parts (A000009). -/
def q (m : ℕ) : ℕ := (Nat.Partition.distincts m).card

/-- The conjecture recorded in A248175, part (i). -/
theorem main : ∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ q (m * n) := by
  sorry

end OMA.S_oeis_a248175

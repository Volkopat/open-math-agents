import Mathlib

/-!
# A248136: Least positive integer m such that m + n divides D(m) + D(n), where D(.) is given by A001850.

Source: https://oeis.org/A248136
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A248136 (Zhi-Wei Sun, Oct 02 2014): a(n) exists for any
n > 0.

Conventions:
* The sequence has offset 1 (data 1, 20, 3, 6, 1, 4, 200, 299, 5, 29, 4, 119, ...).
* D(.) is the sequence A001850: the central Delannoy numbers D(n) = Sum_{k=0..n} C(n,k)*C(n+k,k)
  (1, 3, 13, 63, ...); this is the helper `D`.
* `a(n) exists` means that there is a positive integer m with the stated divisibility (then the
  least such m exists); it is stated directly as the existence of m, without defining a(n).
-/

namespace OMA.S_oeis_a248136

/-- A001850: the central Delannoy numbers D(n) = Sum_{k=0..n} C(n,k)*C(n+k,k). -/
def D (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * (n + k).choose k

/-- The conjecture recorded in A248136. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ D m + D n := by
  sorry

end OMA.S_oeis_a248136

import Mathlib

/-!
# A248139: Least positive integer m such that m + n divides f(m) + f(n), where f(.) is given by A000172.

Source: https://oeis.org/A248139
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A248139 (Zhi-Wei Sun, Oct 02 2014): a(n) exists for any
n > 0.

Conventions:
* The sequence has offset 1 (data 1, 1, 25, 6, 14, 4, 13, 49, 19, 10, 2, 56, ...).
* f(.) is the sequence A000172: the Franel numbers f(n) = Sum_{k=0..n} C(n,k)^3 (1, 2, 10, 56,
  346, ...); this is the helper `f`.
* `a(n) exists` means that there is a positive integer m with the stated divisibility (then the
  least such m exists); it is stated directly as the existence of m, without defining a(n).
-/

namespace OMA.S_oeis_a248139

/-- A000172: the Franel numbers f(n) = Sum_{k=0..n} C(n,k)^3 (1, 2, 10, 56, 346, ...). -/
def f (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k ^ 3

/-- The conjecture recorded in A248139. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ f m + f n := by
  sorry

end OMA.S_oeis_a248139

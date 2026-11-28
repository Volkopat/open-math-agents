import Mathlib

/-!
# A248142: Least positive integer m such that m + n divides A(m) + A(n), where A(.) is given by A005259.

Source: https://oeis.org/A248142
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A248142 (Zhi-Wei Sun, Oct 02 2014): a(n) exists for any
n > 0.

Conventions:
* The sequence has offset 1 (data 1, 1, 7, 2238, 5, 9, 3, 3, 1, 2484, 2, 2, ...).
* A(.) is the sequence A005259: the Apery numbers A(n) = Sum_{k=0..n} C(n,k)^2*C(n+k,k)^2 (1, 5,
  73, 1445, ...); this is the helper `A`.
* `a(n) exists` means that there is a positive integer m with the stated divisibility (then the
  least such m exists); it is stated directly as the existence of m, without defining a(n).
-/

namespace OMA.S_oeis_a248142

/-- A005259: the Apery numbers A(n) = Sum_{k=0..n} C(n,k)^2*C(n+k,k)^2 (1, 5, 73, 1445, ...). -/
def A (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k ^ 2 * (n + k).choose k ^ 2

/-- The conjecture recorded in A248142. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ A m + A n := by
  sorry

end OMA.S_oeis_a248142

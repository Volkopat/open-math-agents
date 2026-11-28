import Mathlib

/-!
# A375351: Least squarefree integer m > 1 such that the product of all those (p + 4)/(p + 2) (with p a prime divisor of m) equals (2*n + 1)/(2*n - 1).

Source: https://oeis.org/A375351
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A375351 (Zhi-Wei Sun, Aug 14 2024): a(n) exists for any
positive integer n.

Conventions:
* The sequence has offset 1 (data 50234415, 1085, 3, 5, 7, 43493, 11, 13, 232087, 17, 19, 579617,
  ...).
* The product is taken over the prime divisors p of m (`Nat.primeFactors m`) and is computed in
  `ℚ`; the right-hand side is the rational number (2*n+1)/(2*n-1).
* `a(n) exists` means that some m with the stated property exists (then the least such m exists);
  it is stated directly as the existence of m, without defining a(n).
-/

namespace OMA.S_oeis_a375351

/-- The conjecture recorded in A375351. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ m : ℕ, 1 < m ∧ Squarefree m ∧
    ∏ p ∈ m.primeFactors, (((p : ℚ) + 4) / ((p : ℚ) + 2)) = (2 * (n : ℚ) + 1) / (2 * n - 1) := by
  sorry

end OMA.S_oeis_a375351

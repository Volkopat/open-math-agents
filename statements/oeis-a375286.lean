import Mathlib

/-!
# A375286: a(n) = f(1) + f(2) + ... + f(n), where f(n) = (-2)^Omega(n) = A165872(n).

Source: https://oeis.org/A375286
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A375286 (Charles R Greathouse IV, Aug 09 2024): |a(n)|
< n for n >= 3078 (conjectured by Zhi-Wei Sun, as recorded in the formula section of the entry).

Conventions:
* The sequence has offset 1 (data 1, -1, -3, 1, -1, 3, 1, -7, -3, 1, -1, -9, ...).
* `a n` is the integer sum of f(k) = (-2)^Omega(k) over k = 1, ..., n.
* Omega(k) is the number of prime factors of k counted with multiplicity, written as the length of
  `Nat.primeFactorsList k`.
* The absolute value is the integer absolute value, and the comparison is made in `ℤ` with n cast.
* The bound 3078 is sharp for the range of the claim: |a(3077)| >= 3077.
-/

namespace OMA.S_oeis_a375286

/-- A375286: a(n) = sum of (-2)^Omega(k) over k = 1..n. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, (-2 : ℤ) ^ (Nat.primeFactorsList k).length

/-- The conjecture recorded in A375286 (Sun): |a(n)| < n for all n >= 3078. -/
theorem main : ∀ n : ℕ, 3078 ≤ n → |a n| < (n : ℤ) := by
  sorry

end OMA.S_oeis_a375286

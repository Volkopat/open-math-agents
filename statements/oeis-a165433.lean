import Mathlib

/-!
# A165433: A transform of the double factorial numbers A001147.

Source: https://oeis.org/A165433
Credit: @agchua

R. J. Mathar (Nov 14 2011), in the formula section of A165433:
  Conjecture: 2*a(n) -3*a(n-1) +(3-2*n)*a(n-2) +(2*n-3)*a(n-3)=0.
The sequence is given by the formula of the entry, a(n) = Sum_{k=0..floor(n/2)} C(n-k,k)*(2k)!/(k!*2^k),
where (2k)!/(k! 2^k) = A001147(k) is the double factorial (2k-1)!!. For k ≤ n/2 the subtraction
n-k is exact. The definition is computed in ℚ, so the division is exact (the values are integers).
The sequence has offset 0 (a(0) = 1). The recurrence uses a(n-3), so the conjecture is stated
for n ≥ 3.
-/

namespace OMA.S_oeis_a165433

/-- A165433(n) = Sum_{k=0..floor(n/2)} C(n-k, k) (2k)! / (k! 2^k). -/
def a (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    ((n - k).choose k : ℚ) * ((2 * k).factorial : ℚ) / ((k.factorial : ℚ) * 2 ^ k)

/-- Mathar's conjecture: for n ≥ 3, 2 a(n) - 3 a(n-1) + (3-2n) a(n-2) + (2n-3) a(n-3) = 0. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    2 * a n - 3 * a (n - 1) + (3 - 2 * (n : ℚ)) * a (n - 2) + (2 * (n : ℚ) - 3) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a165433

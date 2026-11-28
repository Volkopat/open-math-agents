import Mathlib

/-!
# A338857: With S(n,k) = Sum_{n<=j<=k} 1/(2*j+1), a(n)=k+1 such that S(n,k-1) < 1 <= S(n,k) for n>=0 and a(0)=1.

Source: https://oeis.org/A338857
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A338857 (Gerhard Kirchner, Nov 12 2020): a(n) =
ceiling(n*exp(2)+(exp(2)+exp(-2))/(24*n)), verified for n<=3000.

Conventions:
* The sequence has offset 0 (data 1, 8, 15, 23, 30, 38, 45, 52, 60, 67, 74, 82, ...).
* S(n,k) = Sum_{n<=j<=k} 1/(2*j+1) is the rational number `S n k` (sum over `Finset.Icc n k`,
  which is empty and gives 0 when k < n). a(n) = k+1 for the unique k with S(n,k-1) < 1 <= S(n,k);
  the statement says that every such k satisfies k + 1 = ceiling(...). For n >= 1 such a k is at
  least n, so k - 1 is an exact subtraction.
* The formula divides by n, so it is stated for n >= 1 only (a(0) = 1 is a separate convention in
  the OEIS name). exp is `Real.exp` and the ceiling is `Int.ceil`.
-/

namespace OMA.S_oeis_a338857

/-- S(n,k) = Sum_{n <= j <= k} 1/(2j+1). -/
def S (n k : ℕ) : ℚ := ∑ j ∈ Finset.Icc n k, 1 / (2 * (j : ℚ) + 1)

/-- The conjecture recorded in A338857. -/
theorem main : ∀ n k : ℕ, 0 < n → S n (k - 1) < 1 → 1 ≤ S n k →
    (k : ℤ) + 1 = ⌈(n : ℝ) * Real.exp 2 + (Real.exp 2 + Real.exp (-2)) / (24 * n)⌉ := by
  sorry

end OMA.S_oeis_a338857

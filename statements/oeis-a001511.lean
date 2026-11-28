import Mathlib

/-!
# A001511: The ruler function: 2-adic valuation of 2n.

Source: https://oeis.org/A001511
Credit: @rabdelaal

OEIS A001511 records the conjecture (Ivan N. Ianakiev, 2019, proved by Sela Fried,
2025) that for any nonnegative integer `k`, the sum of the `k`-th powers of the even
divisors of `n` is divisible by the sum of the `k`-th powers of the odd divisors of `n`.
-/

namespace OMA.S_oeis_a001511

/-- Sum of `k`-th powers of the even divisors of `n`. -/
def evenDivPow (n k : ℕ) : ℕ :=
  ∑ d ∈ Nat.divisors n, d ^ k * (d % 2 == 0).toNat

/-- Sum of `k`-th powers of the odd divisors of `n`. -/
def oddDivPow (n k : ℕ) : ℕ :=
  ∑ d ∈ Nat.divisors n, d ^ k * (d % 2 == 1).toNat

/-- The conjecture recorded in OEIS A001511 (Ianakiev, proved Fried 2025): the sum of
`k`-th powers of even divisors is divisible by the sum of `k`-th powers of odd divisors
(note `1` is always an odd divisor, so the denominator is positive). -/
theorem main : ∀ (n : ℕ), 0 < n → ∀ k : ℕ, oddDivPow n k ∣ evenDivPow n k := by
  sorry

end OMA.S_oeis_a001511

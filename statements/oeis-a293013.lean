import Mathlib

/-!
# OEIS A293013

`a(n) = n! * [x^n] exp(x / (1 - x)^n)`
`= Sum_{i = 0..n} C(n, i) * (n * (n - i) + i - 1).descFactorial i`.

Conjecture (Peter Bala):
`a(n + k) ≡ a(n) [MOD k]` for all `n >= 0` and `k >= 1`.
-/

namespace OMA.S_oeis_a293013

/-- `a(n) = Sum_{i = 0..n} C(n, i) * (n * (n - i) + i - 1).descFactorial i`. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1),
    Nat.choose n i * (n * (n - i) + i - 1).descFactorial i

theorem main : ∀ n k : ℕ, 1 ≤ k → a (n + k) ≡ a n [MOD k] := by
  sorry

end OMA.S_oeis_a293013

import Mathlib

/-!
# A023365: a(n) = 2^(3^(n-1))

Source: https://oeis.org/A023365
Credit: @jagong-cmu

Formalizes the OEIS A023365 conjecture of Steven Finch (Oct 08 2024):
a(n+1) is conjectured to be the reduced denominator of b(n) = b(n-1)*(3/2 - b(n-1)^2); b(0) = 1/2.

Conventions:
* The sequence `a` is defined literally from the OEIS name, with offset 1. The exponent `n - 1`
  is truncated subtraction on `ℕ`, which is exact for `n >= 1`. Only `a (n + 1)` is used.
* The auxiliary sequence `b` is defined in `ℚ` by the recurrence of the conjecture.
* The reduced denominator of a rational number `q` is `q.den` (Mathlib keeps every `ℚ` value in
  lowest terms with a positive denominator).
* The claim is stated for every `n >= 0`, which is the full range of `b`.
-/

namespace OMA.S_oeis_a023365

/-- `a(n) = 2^(3^(n-1))`, offset 1. -/
def a (n : ℕ) : ℕ := 2 ^ (3 ^ (n - 1))

/-- `b(0) = 1/2` and `b(n) = b(n-1) * (3/2 - b(n-1)^2)`. -/
def b : ℕ → ℚ
  | 0 => 1 / 2
  | n + 1 => b n * (3 / 2 - b n ^ 2)

/-- For every `n >= 0`, the reduced denominator of `b(n)` is `a(n+1)`. -/
theorem main : ∀ n : ℕ, ((b n).den : ℕ) = a (n + 1) := by
  sorry

end OMA.S_oeis_a023365

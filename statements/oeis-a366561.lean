import Mathlib

/-!
# A366561: T(n,k) = number of (x, y) in [1, n]^2 with gcd(x^2 - y^2, n) = k

Source: https://oeis.org/A366561 (conjecture of Ridouane Oudra, Jun 17 2025)

The triangle has rows `n >= 1` and columns `1 <= k <= n`, with
`T(n,k) = Sum_{y=1..n} Sum_{x=1..n} [gcd(x^2 - y^2, n) = k]`; the gcd is taken of the
integer `x^2 - y^2` and `n` (it is nonnegative, and `gcd(0, n) = n`).

Conjecture (the first of the conjectures of Ridouane Oudra listed in the entry):
`T(n,k) = 0` if and only if `k` does not divide `n`.
-/

namespace OMA.S_oeis_a366561

/-- `T n k` counts the pairs `(x, y)` with `1 <= x, y <= n` and `gcd(x^2 - y^2, n) = k`. -/
def T (n k : ℕ) : ℕ :=
  ∑ y ∈ Finset.Icc 1 n, ∑ x ∈ Finset.Icc 1 n,
    if Int.gcd ((x : ℤ) ^ 2 - (y : ℤ) ^ 2) (n : ℤ) = k then 1 else 0

theorem main : ∀ n k : ℕ, 1 ≤ k → k ≤ n → (T n k = 0 ↔ ¬ k ∣ n) := by
  sorry

end OMA.S_oeis_a366561

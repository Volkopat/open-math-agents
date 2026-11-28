import Mathlib

/-!
# A232270: Number of ways to write n = x + y (0 < x <= y) with sigma(x) + phi(y) prime, where sigma(x) is the sum of all (positive) divisors of x and phi is Euler's totient function.

Source: https://oeis.org/A232270
Credit: @keiichisince1986-bot

A232270 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 1, and a(n) = 1 only for n = 2, 3, 4, 29, 70, 105. [Part (ii)
of the entry, with sigma(x) + sigma(y), is not formalized here.]

Conventions:
- `sigma(x)` is `ArithmeticFunction.sigma 1 x` and `phi` is `Nat.totient`.
- `n = x + y` with `0 < x ≤ y` means `1 ≤ x ≤ n/2` (floor division) and `y = n - x`; so `a n` counts
  the `x ∈ [1, n/2]` with `sigma(x) + phi(n - x)` prime.
- `a(n) = 1 only for n = 2, 3, 4, 29, 70, 105` is read as: the set of `n` with `a(n) = 1` is exactly
  `{2, 3, 4, 29, 70, 105}` (each of these has `a(n) = 1` in the data).
-/

namespace OMA.S_oeis_a232270

/-- `a n` is the number of ways to write `n = x + y` with `0 < x ≤ y` and `sigma(x) + phi(y)` prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (n / 2)).filter
    (fun x => (ArithmeticFunction.sigma 1 x + Nat.totient (n - x)).Prime)).card

theorem main :
    (∀ n : ℕ, 1 < n → 0 < a n) ∧ {n : ℕ | a n = 1} = {2, 3, 4, 29, 70, 105} := by
  sorry

end OMA.S_oeis_a232270

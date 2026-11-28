import Mathlib

/-!
# A248029: least m such that m + n divides phi(m)*sigma(n)

Source: https://oeis.org/A248029

A248029 (offset 2): `a(n)` is the least positive integer `m` such that `m + n` divides
`phi(m)*sigma(n)`, where `phi` is Euler's totient function (A000010) and `sigma` is the sum of
divisors function (A000203): 1, 1, 3, 1, 6, 1, 7, 4, 8, 1, 2, 1, 10, …  For example `a(8) = 7`
since `7 + 8 = 15` divides `phi(7)*sigma(8) = 6*15 = 90`.

Conjecture (Zhi-Wei Sun, Sep 29 2014): for any `n > 1`, we have `a(n) ≤ n`. (The entry notes
that the existence of `a(n)` is easy, since `m = sigma(n) - n` works.)

Since `a(n)` is the least positive `m` with `m + n` dividing `phi(m)*sigma(n)`, `a(n) ≤ n` holds
exactly when some `m` with `0 < m ≤ n` has this property, and the conjecture is stated in that
form.

Conventions: `phi` is `Nat.totient` and `sigma(n)` is written as the divisor sum
`∑ d ∈ n.divisors, d`. Everything is in `ℕ`.
-/

namespace OMA.S_oeis_a248029

theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ m : ℕ, 0 < m ∧ m ≤ n ∧ (m + n) ∣ Nat.totient m * ∑ d ∈ n.divisors, d := by
  sorry

end OMA.S_oeis_a248029

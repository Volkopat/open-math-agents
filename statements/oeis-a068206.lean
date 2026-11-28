import Mathlib

/-!
# A068206: Bernoulli numerator and denominator gcd equal to 7

Source: https://oeis.org/A068206
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A068/A068206.seq
Credit: @Bondyboy2001

Let `N(2n)` be the numerator of the Bernoulli number `B(2n)` and `D(2n)` its denominator.
The sequence consists of the positive integers `n` for which `gcd(N(2n), D(2n-2)) = 7`.
Vaclav Kotesovec conjectured in the OEIS entry that every term has the form `7 + 21*j`.

The absolute numerator is used, since changing the sign of a Bernoulli numerator does not change
the relevant positive greatest common divisor.
-/

namespace OMA.S_oeis_a068206

/-- Membership in A068206. -/
def IsTerm (n : ℕ) : Prop :=
  Nat.gcd (bernoulli (2 * n)).num.natAbs (bernoulli (2 * n - 2)).den = 7

theorem main : ∀ n : ℕ, 1 ≤ n → IsTerm n → ∃ j : ℕ, n = 7 + 21 * j := by
  sorry

end OMA.S_oeis_a068206

import Mathlib

/-!
# A055272: First differences of 7^n (A000420).

Source: https://oeis.org/A055272
Credit: @bnb9001

a(0) = 1 and a(n) = 7^n - 7^(n-1) = 6*7^(n-1) for n >= 1 (offset 0: 1, 6, 42, 294, ...).

Conjecture (De Koninck and Mercier, Introduction a la theorie des nombres): for n >= 1, a(n) is
the period length of the decimal expansion of 1/7^n. The entry notes that the conjecture holds:
10 is a primitive root modulo 7^n. Since gcd(10, 7^n) = 1, the decimal expansion of 1/7^n is purely
periodic and its period length is the multiplicative order of 10 modulo 7^n, which is how the
period length is defined below.
-/

namespace OMA.S_oeis_a055272

/-- A055272: first differences of `7^n` (with `a 0 = 1`). -/
def a (n : ℕ) : ℕ := if n = 0 then 1 else 7 ^ n - 7 ^ (n - 1)

/-- The period length of the decimal expansion of `1/m` for `m` coprime to 10: the multiplicative
order of 10 modulo `m`. -/
noncomputable def period (m : ℕ) : ℕ := orderOf (10 : ZMod m)

/-- The conjecture, proved: for `n >= 1`, the period length of `1/7^n` is `a(n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → period (7 ^ n) = a n := by
  sorry

end OMA.S_oeis_a055272

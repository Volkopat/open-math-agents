import Mathlib

/-!
# A164848: the quotient A026741(n)/A051712(n+1) is periodic with period 24

Source: https://oeis.org/A164848
Credit: @sntntHb

`a(n) = A026741(n) / A051712(n+1)` (offset 1), where
* A026741(n) is `n` for odd `n` and `n/2` for even `n`, i.e. `n / gcd(n, 2)`;
* A051712(m) is the numerator of `b(m) - b(m+1)`, where `b(m) = m/((m+1)(m+2))`.
The first terms are `1, 1, 3, 2, 1, 3, 1, 4, 3, 1, 1, 6, ...`. The entry records the conjecture
(checked for the first 3000 terms there)
  `a(n)` is periodic with `a(n+24) = a(n)`.

The numerator is Mathlib's `Rat.num` of the rational number `b(m) - b(m+1)`, an integer; the
quotient is taken in the integers (the division is exact for `n ≥ 1`, as stated in the entry's
definition). The periodicity is stated for every `n ≥ 1`.
-/

namespace OMA.S_oeis_a164848

/-- A026741: `n / gcd(n, 2)`. -/
def A026741 (n : ℕ) : ℕ := n / Nat.gcd n 2

/-- `b m = m / ((m+1)(m+2))`. -/
def b (m : ℕ) : ℚ := (m : ℚ) / (((m : ℚ) + 1) * ((m : ℚ) + 2))

/-- A051712: the numerator of `b(m) - b(m+1)`. -/
def A051712 (m : ℕ) : ℤ := (b m - b (m + 1)).num

/-- `a n = A026741(n) / A051712(n+1)` (OEIS A164848). -/
def a (n : ℕ) : ℤ := (A026741 n : ℤ) / A051712 (n + 1)

/-- The conjecture in OEIS A164848: `a(n+24) = a(n)` for all `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a (n + 24) = a n := by
  sorry

end OMA.S_oeis_a164848

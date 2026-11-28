import Mathlib

/-!
# A007820: Stirling numbers of second kind S(2n,n).

Source: https://oeis.org/A007820
Credit: @divmxnd0x

Conjecture (Peter Bala, Mar 30 2025, stated in A007820): `a(2n+1)` is divisible by `(2n+1)^2`.

Formalization notes:
* `a n = S(2n, n)` with Mathlib's Stirling numbers of the second kind `Nat.stirlingSecond`
  (offset 0: `a 0, a 1, ... = 1, 1, 7, 90, 1701, ...`).
* The conjecture is stated for every `n ≥ 0`.
-/

namespace OMA.S_oeis_a007820

/-- A007820(n) = S(2n, n). -/
def a (n : ℕ) : ℕ := Nat.stirlingSecond (2 * n) n

/-- Bala's conjecture: `(2n+1)^2` divides `a(2n+1)`. -/
theorem main : ∀ n : ℕ, (2 * n + 1) ^ 2 ∣ a (2 * n + 1) := by
  sorry

end OMA.S_oeis_a007820

import Mathlib

/-!
# A007226: a(n) = 2/(n+1) * binomial(3n, n).

Source: https://oeis.org/A007226
Credit: @rabdelaal

The Fuss-Catalan numbers `2/(n+1) * C(3n, n)` (OEIS A007226; equivalently
`(2n+1) * A000139(n)`).

OEIS A007226 records the conjecture (Peter Bala, 2023) that `a(n)` is odd iff `n` is a
term of A022341: an odd number whose binary expansion has no two adjacent `1` bits.
-/

namespace OMA.S_oeis_a007226

/-- The OEIS A007226 entry: `2/(n+1) * binomial(3n, n)`; the division is exact. -/
def a (n : ℕ) : ℕ := 2 * Nat.choose (3 * n) n / (n + 1)

/-- `k` is an odd Fibbinary number (A022341). -/
def IsOddFibbinary (k : ℕ) : Prop :=
  k % 2 = 1 ∧ Nat.land k (k / 2) = 0

/-- The conjecture recorded in OEIS A007226 (Bala): `a n` is odd iff `n` is an odd
Fibbinary number. -/
theorem main : ∀ n : ℕ, a n % 2 = 1 ↔ IsOddFibbinary n := by
  sorry

end OMA.S_oeis_a007226

import Mathlib

/-!
# A067745: Numerator of ((3*n - 2)/(n^(2*n - 1)*(2*n - 1)*4^(n - 1))).

Source: https://oeis.org/A067745
Credit: @ShoQo

Conjecture (Ralf Stephan, Nov 18 2010): Odd part of 3n-2.

Formalization notes:
* Offset 1: `a n` is defined for `n ≥ 1`, where all exponents and the factor `2n - 1` are
  positive; the fraction is computed in `ℚ` and `a n` is its numerator in lowest terms.
* The odd part of `m` is `m / 2^(v_2(m))`, with `v_2` given by `Nat.factorization`.
* Robert Israel (May 16 2017) sketches a proof in the entry.
-/

namespace OMA.S_oeis_a067745

/-- a(n): the numerator of `(3n - 2) / (n^(2n-1) * (2n - 1) * 4^(n-1))`. -/
def a (n : ℕ) : ℤ :=
  ((3 * (n : ℚ) - 2) / ((n : ℚ) ^ (2 * n - 1) * (2 * (n : ℚ) - 1) * 4 ^ (n - 1))).num

/-- The odd part of `m`: `m` with all factors of 2 removed. -/
def oddPart (m : ℕ) : ℕ := m / 2 ^ m.factorization 2

theorem main : ∀ n : ℕ, 1 ≤ n → a n = (oddPart (3 * n - 2) : ℤ) := by
  sorry

end OMA.S_oeis_a067745

import Mathlib

/-!
# A230040: n = x + y + z with 6x-1, 6y-1, 6z-1, 6xy-1, 6xz-1 all Sophie Germain primes

Source: https://oeis.org/A230040

A230040 (offset 1): `a(n)` is the number of ways to write `n = x + y + z` with `y ≤ z` such that
all the five numbers `6*x-1`, `6*y-1`, `6*z-1`, `6*x*y-1` and `6*x*z-1` are Sophie Germain
primes. For example `a(4) = 2`, since `4 = 1 + 1 + 2 = 2 + 1 + 1`, and `6*1-1 = 5` and
`6*2-1 = 11` are Sophie Germain primes.

Conjecture (Zhi-Wei Sun, Oct 06 2013): `a(n) > 0` for all `n > 2`. The entry notes that this has
been verified for `n` up to `10^8`, and that it implies that `6*n - 3` with `n > 2` is a sum of
three Sophie Germain primes.

Since `a(n)` counts the triples `(x, y, z)` with `x + y + z = n`, `y ≤ z` and the five numbers
Sophie Germain primes, `a(n) > 0` says exactly that such a triple exists, and the conjecture is
stated in that form.

Conventions:
- A Sophie Germain prime is a prime `p` such that `2p + 1` is also prime.
- `x, y, z` range over `ℕ`. They are automatically positive: if one of them is `0`, the
  corresponding `6*x - 1`, `6*y - 1` or `6*z - 1` is `0` in `ℕ` (and `-1` in `ℤ`), which is not
  prime. For positive values all the subtractions are exact.
-/

namespace OMA.S_oeis_a230040

/-- A Sophie Germain prime: a prime `p` with `2p + 1` also prime. -/
def IsSophieGermain (p : ℕ) : Prop := Nat.Prime p ∧ Nat.Prime (2 * p + 1)

theorem main :
    ∀ n : ℕ, 2 < n →
      ∃ x y z : ℕ, x + y + z = n ∧ y ≤ z ∧
        IsSophieGermain (6 * x - 1) ∧ IsSophieGermain (6 * y - 1) ∧ IsSophieGermain (6 * z - 1) ∧
        IsSophieGermain (6 * x * y - 1) ∧ IsSophieGermain (6 * x * z - 1) := by
  sorry

end OMA.S_oeis_a230040

import Mathlib

/-!
# A237597: a(n) = |{0 < k < prime(n): n divides pi(k*n)}|, where pi(.) is given by A000720.

Source: https://oeis.org/A237597
Credit: @ceejcake

Conjecture (Zhi-Wei Sun, 2014, stated in the OEIS entry): `a(n) > 0` for all `n > 0`.

Formalization notes:
* The sequence has offset `1`; `a n` is defined for all `n : ℕ` and the conjecture is stated for
  `0 < n`.
* `prime(n)` is the `n`-th prime with `prime(1) = 2`; in Mathlib this is
  `Nat.nth Nat.Prime (n - 1)` (`Nat.nth` is `0`-indexed).
* `pi(x)` (A000720) is the number of primes `≤ x`, which is Mathlib's `Nat.primeCounting x`
  (not `Nat.primeCounting'`, which counts primes `< x`).
* `a n` counts the `k` with `0 < k < prime(n)` such that `n ∣ pi(k * n)`; these `k` lie in
  `Finset.Ioo 0 (prime n)`.
* Initial values for `n = 1, 2, ..., 16`:
  `a(n) = 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 3, 3, 2, 4, 3, 3, ...`; for example `a(6) = 1` since
  `pi(11 * 6) = 18 = 3 * 6` with `11 < prime(6) = 13`.
-/

namespace OMA.S_oeis_a237597

/-- `prime n` is the `n`-th prime, `1`-indexed: `prime 1 = 2`, `prime 2 = 3`, ... -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `a n` is the number of `k` with `0 < k < prime(n)` such that `n` divides `pi(k * n)`
(OEIS A237597). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 (prime n)).filter fun k => n ∣ Nat.primeCounting (k * n)).card

/-- OEIS A237597 conjecture (Zhi-Wei Sun): `a n > 0` for every `n > 0`. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a237597

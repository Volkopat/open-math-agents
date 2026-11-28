import Mathlib

/-!
# A219025: primes p < n with 6n - p and 6n + p both prime

Source: https://oeis.org/A219025

A219025 (offset 1): `a(n)` is the number of primes `p < n` such that `6n - p` and `6n + p` are
both prime: 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 1, 2, …

Conjecture (Zhi-Wei Sun, Nov 10 2012): `a(n) > 0` for all `n = 6, 7, …`. The entry notes that
this has been verified for `n` up to `10^8`.

Since `a(n)` counts the primes `p < n` with `6n - p` and `6n + p` prime, `a(n) > 0` says exactly
that such a prime exists, and the conjecture is stated in that form. The general conjecture on
integer-valued polynomials listed afterwards in the entry (for `n` large enough) is a separate
claim and is not part of this statement.

Conventions: everything is in `ℕ`; the subtraction `6n - p` is exact because `p < n ≤ 6n`.
-/

namespace OMA.S_oeis_a219025

theorem main :
    ∀ n : ℕ, 6 ≤ n →
      ∃ p : ℕ, p < n ∧ Nat.Prime p ∧ Nat.Prime (6 * n - p) ∧ Nat.Prime (6 * n + p) := by
  sorry

end OMA.S_oeis_a219025

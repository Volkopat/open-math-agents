import Mathlib

/-!
# A224030: 0 < k < n with 2n + k and 2n^3 + k^3 both prime

Source: https://oeis.org/A224030

A224030 (offset 1): `a(n) = |{0 < k < n : 2*n + k and 2*n^3 + k^3 are both prime}|`.
For example `a(7) = 1` since `2*7 + 5 = 19` and `2*7^3 + 5^3 = 811` are both prime.

Conjecture (Zhi-Wei Sun, Apr 15 2013): `a(n) > 0` for all `n > 4`. The entry notes that this has
been verified for `n` up to `10^8`.

Since `a(n)` counts the `0 < k < n` with `2n + k` and `2n^3 + k^3` both prime, `a(n) > 0` says
exactly that such a `k` exists, and the conjecture is stated in that form. The entry's further
conjecture (some `0 < k < n` with `n^2 + k^2` prime, for `n > 1`) is a separate claim and is not
part of this statement.

Conventions: everything is in `ℕ`; no subtraction occurs.
-/

namespace OMA.S_oeis_a224030

theorem main :
    ∀ n : ℕ, 4 < n →
      ∃ k : ℕ, 0 < k ∧ k < n ∧ Nat.Prime (2 * n + k) ∧ Nat.Prime (2 * n ^ 3 + k ^ 3) := by
  sorry

end OMA.S_oeis_a224030

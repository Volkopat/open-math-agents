import Mathlib

/-!
# A282459: composite numbers of the form 2n - 2^k + 1

Source: https://oeis.org/A282459

A282459 (offset 0): `a(n)` is the number of composite numbers of the form `2*n - 2^k + 1`
(`k > 0`, `2^k < 2*n + 1`): 0, 0, 0, 0, 0, 1, 1, 0, 2, 1, 0, 2, 2, 1, 3, …  For example
`a(7) = 0` because `15 - 2 = 13`, `15 - 4 = 11` and `15 - 8 = 7` are prime numbers.

Conjecture (Altug Alkan, Feb 15 2017): `a(n) > 0` for all `n > 52`. (The entry points to the
related conjecture in A039669.)

Since `a(n)` counts the `k > 0` with `2^k < 2n + 1` and `2n + 1 - 2^k` composite, `a(n) > 0`
says exactly that such a `k` exists, and the conjecture is stated in that form.

Conventions:
- A composite number is an integer greater than `1` that is not prime.
- Everything is in `ℕ`; `2*n + 1 - 2^k` is an exact subtraction because `2^k < 2*n + 1`.
- The bound is sharp in the sense that `a(52) = 0`.
-/

namespace OMA.S_oeis_a282459

theorem main :
    ∀ n : ℕ, 52 < n →
      ∃ k : ℕ, 0 < k ∧ 2 ^ k < 2 * n + 1 ∧ 1 < 2 * n + 1 - 2 ^ k ∧
        ¬ Nat.Prime (2 * n + 1 - 2 ^ k) := by
  sorry

end OMA.S_oeis_a282459

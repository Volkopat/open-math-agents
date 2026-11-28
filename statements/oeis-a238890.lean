import Mathlib

/-!
# OEIS A238890, conjecture (i)

Source: https://oeis.org/A238890
For each positive `n`, count the indices `1 ≤ k ≤ n` for which the `(k * n)`-th
prime minus the number of primes at most `k * n` is prime. The count is always
positive and differs from one when `n > 28`.
-/

namespace OMA.S_oeis_a238890

-- Mathlib starts indexing primes at zero, so the first prime is at index zero.
noncomputable def countPrimeDifferences (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter fun k =>
    Nat.Prime (Nat.nth Nat.Prime (k * n - 1) - Nat.primeCounting (k * n))).card

theorem main :
    (∀ n : ℕ, 0 < n → 0 < countPrimeDifferences n) ∧
    (∀ n : ℕ, 28 < n → countPrimeDifferences n ≠ 1) := by
  sorry

end OMA.S_oeis_a238890

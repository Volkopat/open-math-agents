import Mathlib

/-!
# OEIS A308376: k + k^(-1) mod p a square (or a triangular number)

Source: https://oeis.org/A308376
Conjecture: Zhi-Wei Sun.
Credit: @biondadave

A308376(n) is the least positive integer `k < prime(n)` such that `k + k'` is a square, where
`k'` is the unique integer with `0 < k' < prime(n)` and `k k' ≡ 1 (mod prime(n))`, or `0` if
such a number `k` does not exist.

Conjecture 1: `a(n) = 0` only for `n = 1, 3, 4, 5, 14, 22`. In other words, if `p` is a prime not
among `2, 5, 7, 11, 43, 79`, then there are `k` and `m` among `1, ..., p-1` with
`k m ≡ 1 (mod p)` such that `k + m` is a square.
Conjecture 2: for any prime `p > 18`, there are `k` and `m` among `1, ..., p-1` with
`k m ≡ 1 (mod p)` such that `k + m` is a triangular number.

Formalization notes:
* `main` is the conjunction of the two conjectures, in their "in other words" form.
  (That `a(n) = 0` does hold at the six listed indices is part of the data, not of the
  conjecture.)
* A triangular number is `t(t+1)/2` with `t ≥ 0`.
-/

namespace OMA.S_oeis_a308376

theorem main :
    (∀ p : ℕ, p.Prime → p ∉ ({2, 5, 7, 11, 43, 79} : Finset ℕ) →
      ∃ k m : ℕ, 1 ≤ k ∧ k ≤ p - 1 ∧ 1 ≤ m ∧ m ≤ p - 1 ∧ k * m ≡ 1 [MOD p] ∧
        IsSquare (k + m)) ∧
    (∀ p : ℕ, p.Prime → 18 < p →
      ∃ k m : ℕ, 1 ≤ k ∧ k ≤ p - 1 ∧ 1 ≤ m ∧ m ≤ p - 1 ∧ k * m ≡ 1 [MOD p] ∧
        ∃ t : ℕ, k + m = t * (t + 1) / 2) := by
  sorry

end OMA.S_oeis_a308376

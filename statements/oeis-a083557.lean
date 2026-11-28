import Mathlib

/-!
# A083557: a(n) is the greatest prime factor of 3*a(n-1)+2.

Source: https://oeis.org/A083557
Credit: @gblacher2

Conjecture (comment in A083557): "if a(1)=m then the sequence becomes cyclic, for any m."
The same entry notes that the conjecture was verified up to 25000000 by Jud McCranie
(Jun 11 2003).

Conventions:
* `gpf n` is the greatest prime factor of `n`, the maximum of `Nat.primeFactors n`.
  Along an orbit it is only applied to numbers of the form `3 * x + 2 ≥ 2`, which always
  have a prime factor.
* `orbit m` is the sequence of the recurrence started at `a(1) = m`, shifted to start at
  index `0`: `orbit m 0 = m` and `orbit m (n + 1) = gpf (3 * orbit m n + 2)`.
  The sequence A083557 itself is `orbit 3`, with terms `3, 11, 7, 23, 71, 43, ...`.
* "for any m" is read over the positive integers `m`, as the terms of the OEIS sequence
  (offset 1) are positive integers.
* "becomes cyclic" is read as "is eventually periodic": there are an index `N` and a
  period `p > 0` with `orbit m (n + p) = orbit m n` for every `n ≥ N`.
-/

namespace OMA.S_oeis_a083557

/-- The greatest prime factor of `n` (and `0` when `n` has no prime factor, i.e. `n ≤ 1`). -/
def gpf (n : ℕ) : ℕ := n.primeFactors.sup id

/-- The sequence with `a(1) = m` and `a(n) = gpf (3 * a(n-1) + 2)`, indexed from `0`. -/
def orbit (m : ℕ) : ℕ → ℕ
  | 0 => m
  | n + 1 => gpf (3 * orbit m n + 2)

/-- The conjecture: for every positive integer `m`, the sequence with `a(1) = m` becomes
cyclic, that is, it is eventually periodic. -/
theorem main : ∀ m : ℕ, 0 < m →
    ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n → orbit m (n + p) = orbit m n := by
  sorry

end OMA.S_oeis_a083557

import Mathlib

/-!
# A242560: Least positive number k such that (n!-k)/(n-k) is an integer.

Source: https://oeis.org/A242560

Offset 1 (data 2, 1, 2, 2, 4, 3, 6, 4, ...). The quotient is taken in ℤ, so `k > n` (negative
denominator) is allowed, and `k = n` (zero denominator) is excluded. "(n!-k)/(n-k) is an integer"
is expressed as `(n! - k) % (n - k) = 0` in ℤ. `a(m) = k` is stated as: `k` satisfies the
condition for `m`, and every `j` satisfying it has `k ≤ j`.

Formalizes the conjecture stated in the OEIS entry: a(2n) = n (for n >= 1).
-/

namespace OMA.S_oeis_a242560

/-- The defining condition of A242560: `0 < k`, `k ≠ m` and `(m! - k)/(m - k)` is an integer. -/
abbrev good (m k : ℕ) : Prop :=
  0 < k ∧ k ≠ m ∧ ((m.factorial : ℤ) - k) % ((m : ℤ) - k) = 0

/-- The conjecture of A242560: `a(2n) = n`, i.e. `n` is the least `k` with `good (2n) k`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → good (2 * n) n ∧ ∀ k : ℕ, good (2 * n) k → n ≤ k := by
  sorry

end OMA.S_oeis_a242560

import Mathlib

/-!
# A146564: solutions of k n / (k - n) = c and the divisors of n^2

Source: https://oeis.org/A146564
Credit: @sntntHb

`a(n)` (offset 1) is the number of solutions of the equation `k n / (k - n) = c` in integers
`k, c`; as the entry explains, the sequence counts the solutions with `k > 0` and any sign of `c`
(for a prime `p` the solutions are `k = p - 1, p + 1, 2p, p^2 + p`, so `a(p) = 4`). The data starts
`1, 4, 4, 7, 4, 13, 4, 10, 7, 13, ...`. Here `a(n)` is the number of positive integers `k ≠ n` with
`k - n` dividing `k n`.

The entry records the conjecture (R. J. Mathar, Nov 21 2008) `a(n) = A048691(n) + A063647(n)`, where
* `A048691(n) = d(n^2)` is the number of divisors of `n^2`;
* `A063647(n)` is the number of ways to write `1/n` as a difference of exactly two unit fractions,
  `1/n = 1/b - 1/c` with positive integers `b < c` (a way is determined by `b`).
-/

namespace OMA.S_oeis_a146564

/-- OEIS A146564: the number of positive integers `k ≠ n` with `(k - n) ∣ k n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {k : ℕ | 0 < k ∧ k ≠ n ∧ ((k : ℤ) - n) ∣ (k : ℤ) * n}

/-- OEIS A048691: the number of divisors of `n^2`. -/
def A048691 (n : ℕ) : ℕ := (n ^ 2).divisors.card

/-- OEIS A063647: the number of ways to write `1/n` as `1/b - 1/c` with `0 < b < c`. -/
noncomputable def A063647 (n : ℕ) : ℕ :=
  Set.ncard {b : ℕ | 0 < b ∧ ∃ c : ℕ, b < c ∧ (1 : ℚ) / n = 1 / b - 1 / c}

/-- Mathar's conjecture `a(n) = A048691(n) + A063647(n)` for A146564. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = A048691 n + A063647 n := by
  sorry

end OMA.S_oeis_a146564

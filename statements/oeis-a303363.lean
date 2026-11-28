import Mathlib

/-!
# A303363: Number of ways to write n as a*(a+1)/2 + b*(b+1)/2 + 2^c + 2^d, where a,b,c,d are nonnegative integers with a <= b, c <= d and 2|c

Source: https://oeis.org/A303363
Credit: @ceejcake

Conjecture (Zhi-Wei Sun, 2018, OEIS A303363): `a(n) > 0` for all `n > 1`.

Formalization notes:
* The sequence has offset `1`; `a(1) = 0`, which is why the conjecture starts at `n = 2`.
* To avoid shadowing the sequence name `a`, the OEIS variables `a, b` are renamed `x, y`.
  `a n` counts the 4-tuples `(x, y, c, d)` of natural numbers with `x ≤ y`, `c ≤ d`, `c` even
  and `x * (x + 1) / 2 + y * (y + 1) / 2 + 2 ^ c + 2 ^ d = n`. The exponents may be `0`.
* The search bounds are lossless: every summand is at most `n`, so
  `x * (x + 1) / 2 ≤ n` gives `x ^ 2 ≤ 2 * n`, i.e. `x ≤ (2 * n).sqrt` (same for `y`),
  and `2 ^ c ≤ n` gives `c ≤ Nat.log 2 n` (same for `d`; when `n = 0` there is no solution).
* Initial values for `n = 1, ..., 12`: `a(n) = 0, 1, 2, 2, 3, 3, 2, 4, 6, 3, 5, 6`.
-/

namespace OMA.S_oeis_a303363

/-- `a n` is the number of tuples `(x, y, c, d)` of natural numbers with `x ≤ y`, `c ≤ d`,
`c` even and `x * (x + 1) / 2 + y * (y + 1) / 2 + 2 ^ c + 2 ^ d = n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range ((2 * n).sqrt + 1) ×ˢ Finset.range ((2 * n).sqrt + 1) ×ˢ
      Finset.range (Nat.log 2 n + 1) ×ˢ Finset.range (Nat.log 2 n + 1)).filter
    fun ⟨x, y, c, d⟩ =>
      x ≤ y ∧ c ≤ d ∧ 2 ∣ c ∧ x * (x + 1) / 2 + y * (y + 1) / 2 + 2 ^ c + 2 ^ d = n).card

/-- OEIS A303363 conjecture (Zhi-Wei Sun): `a n > 0` for every `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a303363

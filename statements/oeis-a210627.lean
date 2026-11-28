import Mathlib

/-!
# A210627: constants r_n in the study of polynomials of least deviation from zero

Source: https://oeis.org/A210627 (conjecture by R. J. Mathar, Mar 27 2012)

The sequence has offset 3 with `a(3) = 72` (data), and the entry gives, for `n > 3`,
`a(n) = r_n = n * Sum_{k=4..n} k^(n-3) * binomial(n,k) * ((-1)^k*(9*k^2-32*k+24) + k^2)`.
Below `r n` is this formula (used for `n >= 4`, where the entry states it).

A038049(n) is the number of labeled rooted trees with 2-colored leaves; we use the entry's
formula `A038049(n) = Sum_{k=0..n} binomial(n,k) * (n-k)^(n-1)`.

The conjecture: `a(n) = n * A038049(n)`. For `n = 3` this reads `72 = 3 * A038049(3)`; for
`n >= 4` it is `r n = n * A038049(n)`.
-/

namespace OMA.S_oeis_a210627

/-- The entry's formula for `a(n)`, `n > 3`. -/
def r (n : ℕ) : ℤ :=
  n * ∑ k ∈ Finset.Icc 4 n, (k : ℤ) ^ (n - 3) * (n.choose k : ℤ) *
    ((-1) ^ k * (9 * (k : ℤ) ^ 2 - 32 * k + 24) + (k : ℤ) ^ 2)

/-- A038049(n) = Sum_{k=0..n} binomial(n,k)*(n-k)^(n-1). -/
def A038049 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * (n - k) ^ (n - 1)

theorem main : (72 : ℤ) = 3 * A038049 3 ∧ ∀ n : ℕ, 4 ≤ n → r n = n * A038049 n := by
  sorry

end OMA.S_oeis_a210627

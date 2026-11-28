import Mathlib

/-!
# A305499: Square array A(n,k), n > 0 and k > 0, read by antidiagonals, with initial values A(1,k) = k and recurrence equations A(n+1,k) = A(n,k) for 0 < k <= n and A(n+1,k) = A(n,k) - A000035(n+k) for 0 < n < k.

Source: https://oeis.org/A305499
Credit: @agchua

Formula section of A305499 (entry by Werner Schulte, Jun 03 2018):
  Conjecture: Sum_{i=1..n} A(n+1-i,i) = A211538(n+3) for n > 0.
The array is defined exactly by the recurrence of the name line, with A000035(m) = m mod 2.
Row index 0 is not part of the array; the definition below gives it the value 0, and it is never
used, because every row index n+1-i in the sum is at least 1.
A211538 (offset 1) is taken from its own formula line, a(n) = (6*n^2-26*n+25-(2*n-7)*(-1)^n)/16
(Luce Etienne), evaluated in the rationals. This formula reproduces every listed term of A211538 and
agrees with its recurrence, its g.f. and its programs; the conjecture refers to these values (for
n = 1 the sum is A(1,1) = 1 = A211538(4)). (The triple count in the name line of A211538 gives the
listed term of index n+1, not n.)
-/

namespace OMA.S_oeis_a305499

/-- A000035: m mod 2. -/
def A000035 (m : ℕ) : ℤ := ((m % 2 : ℕ) : ℤ)

/-- The square array of A305499: A(1,k) = k, and for n ≥ 1, A(n+1,k) = A(n,k) if k ≤ n and
A(n+1,k) = A(n,k) - A000035(n+k) if n < k. Row 0 is a dummy row. -/
def A : ℕ → ℕ → ℤ
  | 0, _ => 0
  | 1, k => (k : ℤ)
  | n + 2, k => if k ≤ n + 1 then A (n + 1) k else A (n + 1) k - A000035 (n + 1 + k)

/-- A211538 by its formula (6*n^2-26*n+25-(2*n-7)*(-1)^n)/16. -/
def A211538 (n : ℕ) : ℚ :=
  (6 * (n : ℚ) ^ 2 - 26 * (n : ℚ) + 25 - (2 * (n : ℚ) - 7) * (-1 : ℚ) ^ n) / 16

/-- The conjecture: Sum_{i=1..n} A(n+1-i,i) = A211538(n+3) for n > 0. -/
theorem main : ∀ n : ℕ, 0 < n →
    ((∑ i ∈ Finset.Icc 1 n, A (n + 1 - i) i : ℤ) : ℚ) = A211538 (n + 3) := by
  sorry

end OMA.S_oeis_a305499

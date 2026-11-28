import Mathlib

/-!
# A112293: Row sums of number triangle A112292

Source: https://oeis.org/A112293
Credit: @sntntHb

The sequence (offset 0: `1, 2, 7, 36, 253, 2278, ...`) is the row sums of the triangle A112292;
the entry gives the formula `a(n) = Sum_{k=0..n} (2n-1)!!/(2k-1)!!`, which we use as the
definition (with `(-1)!! = 1`; each quotient is an integer, and the sum is computed in `ℚ` so no
truncating division occurs).
The entry records the conjecture (R. J. Mathar, Nov 28 2014):
`Conjecture: a(n) - 2*n*a(n-1) + (2*n-3)*a(n-2) = 0.`

The recurrence involves `a(n-2)`, so it is stated for `n ≥ 2` (offset 0). In Lean, `2 * 0 - 1 = 0`
in `ℕ` and `Nat.doubleFactorial 0 = 1`, so this correctly gives `(-1)!! = 1` at `k = 0`.
-/

namespace OMA.S_oeis_a112293

/-- `a n = ∑_{k=0}^{n} (2n-1)!! / (2k-1)!!` (OEIS A112293). -/
def a (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.doubleFactorial (2 * n - 1) : ℚ) / (Nat.doubleFactorial (2 * k - 1) : ℚ)

/-- R. J. Mathar's conjectured recurrence for OEIS A112293. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    a n - 2 * (n : ℚ) * a (n - 1) + (2 * (n : ℚ) - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a112293

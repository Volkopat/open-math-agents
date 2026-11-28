import Mathlib

/-!
# A175254: a(n) = Sum_{k<=n} A000203(k)*(n-k+1)

Source: https://oeis.org/A175254
Credit: @jagong-cmu

THE CONJECTURE AS STATED IS FALSE. It fails at n = 2: the left side is a(2) = 5,
the right side is A006218(2) + A006218(1) + A006218(0) = 3 + 1 + 0 = 4.

The entry has the formula line
Conjecture: a(n) = Sum_{k=0..n} A006218(n-k). - R. J. Mathar, Oct 17 2012
This file states that line exactly as written, for every n in the OEIS range (offset 1),
so that it can be refuted. Data: a(1..4) = 1, 5, 13, 28. The values of
Sum_{k=0..n} A006218(n-k) for n = 1..4 are 1, 4, 9, 17; they agree only at n = 1.

Conventions:
* `a n = ∑ k ∈ [1, n], σ(k) * (n - k + 1)`, the OEIS name with `A000203 = σ₁`.
  For `k ≤ n` the subtraction `n - k` on `ℕ` is exact.
* `A006218 m = ∑ k ∈ [1, m], ⌊m / k⌋` (offset 0, so `A006218 0 = 0`), with `/` the floor
  division on `ℕ`. The index `n - k` with `k ≤ n` is exact.
-/

namespace OMA.S_oeis_a175254

/-- `a(n) = Sum_{k=1..n} sigma(k) * (n - k + 1)`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.sigma 1 k * (n - k + 1)

/-- A006218: `Sum_{k=1..m} floor(m/k)`, the number of divisors summed up to `m`. -/
def A006218 (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 m, m / k

/-- Mathar's conjecture, as written: `a(n) = Sum_{k=0..n} A006218(n-k)` for all `n ≥ 1`.
It is false (it fails at `n = 2`). -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = ∑ k ∈ Finset.range (n + 1), A006218 (n - k) := by
  sorry

end OMA.S_oeis_a175254

import Mathlib

/-!
# A340424: triangle T(n,k) = A024916(n-k+1)*A002865(k-1), 1 <= k <= n

Source: https://oeis.org/A340424 (conjecture by Omar E. Pol, 2021)

`A024916(m) = Sum_{j=1..m} sigma(j)`, where `sigma` is the sum-of-divisors function
(`ArithmeticFunction.sigma 1`). `A002865(m)` is the number of partitions of `m` that do not
contain 1 as a part (`Nat.Partition m`, with `1 ∉ p.parts`). `A066186(n)` is the sum of all
parts of all partitions of `n`. The triangle has rows `n >= 1` and columns `1 <= k <= n`.

The conjecture: for `n >= 1`, the sum of row `n` equals `A066186(n)`.
-/

namespace OMA.S_oeis_a340424

/-- A024916: `Sum_{j=1..m} sigma(j)`. -/
def A024916 (m : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 m, ArithmeticFunction.sigma 1 j

/-- A002865: the number of partitions of `m` with no part equal to 1. -/
def A002865 (m : ℕ) : ℕ := (Finset.univ.filter fun p : Nat.Partition m => 1 ∉ p.parts).card

/-- A066186: the sum of all parts of all partitions of `n`. -/
def A066186 (n : ℕ) : ℕ := ∑ p : Nat.Partition n, p.parts.sum

/-- A340424: `T(n,k) = A024916(n-k+1)*A002865(k-1)`. -/
def T (n k : ℕ) : ℕ := A024916 (n - k + 1) * A002865 (k - 1)

theorem main : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.Icc 1 n, T n k = A066186 n := by
  sorry

end OMA.S_oeis_a340424

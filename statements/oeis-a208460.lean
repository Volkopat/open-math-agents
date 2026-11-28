import Mathlib

/-!
# A208460: Triangle read by rows: T(n,k) = n minus the k-th proper divisor of n

Source: https://oeis.org/A208460
Credit: @xor2k

Formalizes the precise part of the OEIS A208460 conjecture: one of the divisors of T(n,k) is
also the k-th divisor of n. (The rest of that comment, about a diagram in which the divisors
lie on a 45-degree line so that the divisors of n are predictable, is descriptive and makes no
further precise claim.)

Conventions: rows start at `n = 2` (offset 2). The proper divisors of `n` are the divisors less
than `n` (`Nat.properDivisors n`, as in A027751), listed in increasing order, and `k` runs over
`1, ..., ` the number of proper divisors of `n` (1-based, as in the triangle). The k-th divisor
of `n` is the k-th entry of `Nat.divisors n` in increasing order. The claim that the k-th
divisor of `n` is one of the divisors of `T(n,k)` is stated as divisibility.
-/

namespace OMA.S_oeis_a208460

/-- The k-th (1-based) proper divisor of `n` in increasing order. -/
def kthProperDivisor (n k : ℕ) : ℕ :=
  ((Nat.properDivisors n).sort).getD (k - 1) 0

/-- The k-th (1-based) divisor of `n` in increasing order. -/
def kthDivisor (n k : ℕ) : ℕ :=
  ((Nat.divisors n).sort).getD (k - 1) 0

/-- The triangle entry `T(n,k) = n - (k-th proper divisor of n)`. -/
def T (n k : ℕ) : ℕ :=
  n - kthProperDivisor n k

/-- For every row `n ≥ 2` and every position `k` of that row, the k-th divisor of `n`
divides `T(n,k)`. -/
theorem main :
    ∀ n k : ℕ, 2 ≤ n → 1 ≤ k → k ≤ (Nat.properDivisors n).card →
      kthDivisor n k ∣ T n k := by
  sorry

end OMA.S_oeis_a208460

import Mathlib

/-!
# A277312: Smallest k such that k - lambda(k) = prime(n), where lambda(k) = A002322(k).

Source: https://oeis.org/A277312
Credit: @eltociear

`a(n)` (offset 1) is the least `k` with `k - λ(k) = prime(n)`, where `λ` is the Carmichael
function (A002322) and `prime(n)` the `n`-th prime (`4, 9, 25, 49, 15, 169, ...`). The entry
conjectures:

  a(n) = prime(n)^2 for infinitely many n.

`main` states that the set of such `n` is infinite. `λ` is `ArithmeticFunction.carmichael`; for
`k ≥ 1`, `λ(k) ≤ k`, so `k - λ(k)` is exact there (for `k = 0` it is `0`, which is never a prime).
`a n` is the `sInf` of the admissible `k` (`k = prime(n)^2` is always admissible, since
`λ(p^2) = p(p - 1)`). `prime(k)` is `Nat.nth Nat.Prime (k - 1)`.
-/

namespace OMA.S_oeis_a277312

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- OEIS A277312: the least `k` with `k - λ(k) = prime(n)`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | k - ArithmeticFunction.carmichael k = prime n}

/-- The conjecture in OEIS A277312: `a(n) = prime(n)^2` for infinitely many `n`. -/
theorem main : {n : ℕ | 1 ≤ n ∧ a n = prime n ^ 2}.Infinite := by
  sorry

end OMA.S_oeis_a277312

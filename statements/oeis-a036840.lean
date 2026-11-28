import Mathlib

/-!
# A036840: the phi/sigma tug-of-war is eventually periodic

Source: https://oeis.org/A036840
Credit: @jagraj28

A036840 is built from the "phi/sigma tug-of-war sequence with seed n":
`T(n,1) = phi(n)`, and for `k ≥ 2`, `T(n,k) = phi(T(n,k-1))` if `k` is odd and
`T(n,k) = sigma(T(n,k-1))` if `k` is even. `a(n)` is the rounded average of the repeating terms
if `{T(n,k)}` is eventually periodic, and 0 otherwise. The entry records the conjecture: `a(n)` is
never 0, that is, the sequence `{T(n,k)}` is eventually periodic for every `n`.

`main` states: for every `n ≥ 1` (the offset of the sequence) there are `N` and `P > 0` with
`T(n, k + P) = T(n, k)` for all `k ≥ N`.

Conventions: `T n k` is defined for all `k` with `T n 0 = n`; the step from `k` to `k + 1`
applies `phi` when `k` is even and `sigma` when `k` is odd, so `T n 1 = phi n`,
`T n 2 = sigma (phi n)`, matching the source for `k ≥ 1`. Adding the term `T n 0 = n` in front
does not change eventual periodicity. For example `T 5` runs 5, 4, 7, 6, 12, 4, 7, 6, 12, ...
-/

namespace OMA.S_oeis_a036840

/-- `sigma m`: the sum of the divisors of `m`. -/
def sigma (m : ℕ) : ℕ := ∑ d ∈ m.divisors, d

/-- The phi/sigma tug-of-war sequence with seed `n`. -/
def T (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => if Even k then Nat.totient (T n k) else sigma (T n k)

/-- The conjecture in OEIS A036840. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ N P : ℕ, 0 < P ∧ ∀ k, N ≤ k → T n (k + P) = T n k := by
  sorry

end OMA.S_oeis_a036840

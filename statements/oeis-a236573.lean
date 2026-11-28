import Mathlib

/-!
# A236573: Number of ordered ways to write n = k + m (k > 0, m > 0) such that p = 2*k + phi(m) - 1, prime(p + 2) + 2 and 2*n - p are all prime, where phi(.) is Euler's totient function.

Source: https://oeis.org/A236573
Credit: @eltociear

`a(n)` (offset 1) counts the ordered ways to write `n = k + m` with `k, m > 0` such that
`p = 2k + φ(m) - 1`, `prime(p + 2) + 2` and `2n - p` are all prime. The entry conjectures
(Zhi-Wei Sun):

  a(n) > 0 for all n > 712.

`main` states that such `k`, `m` exist for every `n > 712`. `prime(k)` is the `k`-th prime, `Nat.nth Nat.Prime (k - 1)`. `φ` is `Nat.totient`.
`2k + φ(m) ≥ 3`, so `- 1` is exact; `2n - p` is natural subtraction, and `p < 2n` holds whenever
`2n - p` is prime (it is then positive).
-/

namespace OMA.S_oeis_a236573

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The pair `n = k + m` is counted by A236573, with `p = 2k + φ(m) - 1`. -/
noncomputable def Counted (n k m : ℕ) : Prop :=
  0 < k ∧ 0 < m ∧ n = k + m ∧
    let p := 2 * k + Nat.totient m - 1
    p.Prime ∧ (prime (p + 2) + 2).Prime ∧ (2 * n - p).Prime

/-- The conjecture in OEIS A236573: `a(n) > 0` for all `n > 712`. -/
theorem main : ∀ n : ℕ, 712 < n → ∃ k m : ℕ, Counted n k m := by
  sorry

end OMA.S_oeis_a236573

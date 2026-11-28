import Mathlib

/-!
# A236508: a(n) = |{0 < k < n-2: p = 2*phi(k) + phi(n-k)/2 - 1, p + 2, p + 6 and prime(p) + 6 are all prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A236508
Credit: @eltociear

`a(n)` (offset 1) counts the `k` with `0 < k < n - 2` such that `p = 2φ(k) + φ(n - k)/2 - 1`,
`p + 2`, `p + 6` and `prime(p) + 6` are all prime. The entry conjectures (Zhi-Wei Sun):

  a(n) > 0 for all n > 146.

`main` states that such `k` exists for every `n > 146`. Since `k < n - 2`, `n - k ≥ 3` and
`φ(n - k)` is even, so `φ(n - k)/2` is exact. `prime(k)` is the `k`-th prime, `Nat.nth Nat.Prime (k - 1)`. `φ` is `Nat.totient`.
-/

namespace OMA.S_oeis_a236508

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `k` is counted by A236508 at `n`, with `p = 2φ(k) + φ(n - k)/2 - 1`. -/
noncomputable def Counted (n k : ℕ) : Prop :=
  0 < k ∧ k < n - 2 ∧
    let p := 2 * Nat.totient k + Nat.totient (n - k) / 2 - 1
    p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (prime p + 6).Prime

/-- The conjecture in OEIS A236508: `a(n) > 0` for all `n > 146`. -/
theorem main : ∀ n : ℕ, 146 < n → ∃ k : ℕ, Counted n k := by
  sorry

end OMA.S_oeis_a236508

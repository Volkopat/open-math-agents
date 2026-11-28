import Mathlib

/-!
# A236480: a(n) = |{0 < k < n-2: p = 2*phi(k) + phi(n-k)/2 + 1, prime(p) + 2 and prime(prime(p)) + 2 are all prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A236480
Credit: @eltociear

`a(n)` (offset 1) counts the `k` with `0 < k < n - 2` such that `p = 2φ(k) + φ(n - k)/2 + 1`,
`prime(p) + 2` and `prime(prime(p)) + 2` are all prime. The entry conjectures (Zhi-Wei Sun):

  a(n) > 0 for every n = 640, 641, ....

`main` states that such `k` exists for every `n ≥ 640`. Since `k < n - 2`, `n - k ≥ 3` and
`φ(n - k)` is even, so `φ(n - k)/2` is exact. `prime(k)` is the `k`-th prime, `Nat.nth Nat.Prime (k - 1)`. `φ` is `Nat.totient`.
-/

namespace OMA.S_oeis_a236480

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `k` is counted by A236480 at `n`, with `p = 2φ(k) + φ(n - k)/2 + 1`. -/
noncomputable def Counted (n k : ℕ) : Prop :=
  0 < k ∧ k < n - 2 ∧
    let p := 2 * Nat.totient k + Nat.totient (n - k) / 2 + 1
    p.Prime ∧ (prime p + 2).Prime ∧ (prime (prime p) + 2).Prime

/-- The conjecture in OEIS A236480: `a(n) > 0` for all `n ≥ 640`. -/
theorem main : ∀ n : ℕ, 640 ≤ n → ∃ k : ℕ, Counted n k := by
  sorry

end OMA.S_oeis_a236480

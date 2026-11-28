import Mathlib

/-!
# A236192: a(n) = |{0 < k < n: p = phi(k) + phi(n-k)/4 + 1, prime(p)^2 + (2*p)^2 and p^2 + (2*prime(p))^2 are all prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A236192
Credit: @eltociear

`a(n)` (offset 1) counts the `k` with `0 < k < n` such that `p = φ(k) + φ(n - k)/4 + 1`,
`prime(p)^2 + (2p)^2` and `p^2 + (2 prime(p))^2` are all prime. The entry conjectures
(Zhi-Wei Sun), as part (i):

  a(n) > 0 for all n > 370.

`main` states that such `k` exists for every `n > 370`. `p` must be an integer to be prime, so
`4 ∣ φ(n - k)` is required and `φ(n - k)/4` is exact; this reading reproduces the data (the
nonzero terms up to `n = 34` are at `n = 6, 7, 9, …, 14`). `prime(k)` is the `k`-th prime, `Nat.nth Nat.Prime (k - 1)`. `φ` is `Nat.totient`.
-/

namespace OMA.S_oeis_a236192

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `k` is counted by A236192 at `n`, with `p = φ(k) + φ(n - k)/4 + 1`. -/
noncomputable def Counted (n k : ℕ) : Prop :=
  0 < k ∧ k < n ∧ 4 ∣ Nat.totient (n - k) ∧
    let p := Nat.totient k + Nat.totient (n - k) / 4 + 1
    p.Prime ∧ (prime p ^ 2 + (2 * p) ^ 2).Prime ∧ (p ^ 2 + (2 * prime p) ^ 2).Prime

/-- Part (i) of the conjecture in OEIS A236192: `a(n) > 0` for all `n > 370`. -/
theorem main : ∀ n : ℕ, 370 < n → ∃ k : ℕ, Counted n k := by
  sorry

end OMA.S_oeis_a236192

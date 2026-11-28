import Mathlib

/-!
# A236460: Number of ordered ways to write n = k + m with k > 0 and m > 0 such that p = phi(k) + phi(m)/2 - 1, prime(p) + 4 and prime(p) + 6 are all prime, where phi(.) is Euler's totient function.

Source: https://oeis.org/A236460
Credit: @eltociear

`a(n)` (offset 1) counts the ordered ways to write `n = k + m` with `k, m > 0` such that
`p = φ(k) + φ(m)/2 - 1`, `prime(p) + 4` and `prime(p) + 6` are all prime. The entry conjectures
(Zhi-Wei Sun):

  a(n) > 0 for all n > 211.

`main` states that such `k`, `m` exist for every `n > 211`. Here `p` must be an integer to be
prime, so `2 ∣ φ(m)` is required and `φ(m)/2` is exact division; the data is reproduced with this
reading (`a(24) = 1`, the first nonzero term). `prime(k)` is the `k`-th prime, `Nat.nth Nat.Prime (k - 1)`. `φ` is `Nat.totient`.
-/

namespace OMA.S_oeis_a236460

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The pair `n = k + m` is counted by A236460, with `p = φ(k) + φ(m)/2 - 1`. -/
noncomputable def Counted (n k m : ℕ) : Prop :=
  0 < k ∧ 0 < m ∧ n = k + m ∧ 2 ∣ Nat.totient m ∧
    let p := Nat.totient k + Nat.totient m / 2 - 1
    p.Prime ∧ (prime p + 4).Prime ∧ (prime p + 6).Prime

/-- The conjecture in OEIS A236460: `a(n) > 0` for all `n > 211`. -/
theorem main : ∀ n : ℕ, 211 < n → ∃ k m : ℕ, Counted n k m := by
  sorry

end OMA.S_oeis_a236460

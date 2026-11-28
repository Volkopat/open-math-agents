import Mathlib

/-!
# A236468: Number of ordered ways to write n = k + m with k > 0 and m > 0 such that p = phi(k) + phi(m)/2 - 1, p + 2 and prime(p) - 2 are all prime, where phi(.) is Euler's totient function.

Source: https://oeis.org/A236468
Credit: @eltociear

`a(n)` (offset 1) counts the ordered ways to write `n = k + m` with `k, m > 0` such that
`p = φ(k) + φ(m)/2 - 1`, `p + 2` and `prime(p) - 2` are all prime. The entry conjectures
(Zhi-Wei Sun):

  a(n) > 0 for every n = 250, 251, ....

`main` states that such `k`, `m` exist for every `n ≥ 250`. `p` must be an integer to be prime, so
`2 ∣ φ(m)` is required and `φ(m)/2` is exact; this reading reproduces the data. `prime(k)` is the `k`-th prime, `Nat.nth Nat.Prime (k - 1)`. `φ` is
`Nat.totient`. `prime(p) - 2` is exact since `prime(p) ≥ 2`.
-/

namespace OMA.S_oeis_a236468

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The pair `n = k + m` is counted by A236468, with `p = φ(k) + φ(m)/2 - 1`. -/
noncomputable def Counted (n k m : ℕ) : Prop :=
  0 < k ∧ 0 < m ∧ n = k + m ∧ 2 ∣ Nat.totient m ∧
    let p := Nat.totient k + Nat.totient m / 2 - 1
    p.Prime ∧ (p + 2).Prime ∧ (prime p - 2).Prime

/-- The conjecture in OEIS A236468: `a(n) > 0` for all `n ≥ 250`. -/
theorem main : ∀ n : ℕ, 250 ≤ n → ∃ k m : ℕ, Counted n k m := by
  sorry

end OMA.S_oeis_a236468

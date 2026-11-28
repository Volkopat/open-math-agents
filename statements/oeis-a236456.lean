import Mathlib

/-!
# A236456: Number of ordered ways to write n = k + m with k > 0 and m > 0 such that p = phi(k) + phi(n-k)/4 - 1, q = p + 2 and r = prime(q) + 2 are all prime, where phi(.) is Euler's totient function.

Source: https://oeis.org/A236456
Credit: @eltociear

`a(n)` (offset 1) counts the ordered ways to write `n = k + m` with `k, m > 0` such that
`p = φ(k) + φ(n - k)/4 - 1`, `q = p + 2` and `r = prime(q) + 2` are all prime. The entry
conjectures (Zhi-Wei Sun):

  a(n) > 0 for all n > 357.

`main` states that such `k` exists for every `n > 357`. Here `p` must be an integer to be prime,
so `4 ∣ φ(n - k)` is required and `φ(n - k)/4` is exact division; the data is reproduced with this
reading (`a(14) = 1`, the first nonzero term). `prime(k)` is the `k`-th prime, `Nat.nth Nat.Prime (k - 1)`. `φ` is `Nat.totient`.
-/

namespace OMA.S_oeis_a236456

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The pair `n = k + (n - k)` is counted by A236456, with `p = φ(k) + φ(n - k)/4 - 1`. -/
noncomputable def Counted (n k : ℕ) : Prop :=
  0 < k ∧ k < n ∧ 4 ∣ Nat.totient (n - k) ∧
    let p := Nat.totient k + Nat.totient (n - k) / 4 - 1
    p.Prime ∧ (p + 2).Prime ∧ (prime (p + 2) + 2).Prime

/-- The conjecture in OEIS A236456: `a(n) > 0` for all `n > 357`. -/
theorem main : ∀ n : ℕ, 357 < n → ∃ k : ℕ, Counted n k := by
  sorry

end OMA.S_oeis_a236456

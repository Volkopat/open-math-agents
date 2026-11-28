import Mathlib

/-!
# A369425: Expansion of Sum_{n>=1} x^(n*(n+1)/2)*((1+x)/(1-x))^n.

Source: https://oeis.org/A369425
Credit: @thtsben2

Conjecture (Mikhail Kurkov, OEIS, Jun 13 2026):
`a(n) = b(n) - b(n - 2)` for all `n ≥ 1`, where
`b(n) = ∑_{k=1}^{n} A142978(n - k + 1, A003056(k))` (with `b(0) = 0`),
`A142978(n, k) = ∑_{i=0}^{n-1} C(n - 1, i) * C(k + i, n)`, and
`A003056(k) = ⌊(√(1 + 8k) - 1) / 2⌋` (the largest `m` with `m(m + 1)/2 ≤ k`).
-/

namespace OMA.S_oeis_a369425

open PowerSeries

/-- `1 / (1 - X)` in `PowerSeries ℤ`. -/
def invOneSub : PowerSeries ℤ := mk fun _ => 1

/-- `A369425(n)`: coefficient of `x^n` in `∑_{m≥1} x^{m(m+1)/2} ((1+x)/(1-x))^m`. -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.Icc 1 n, coeff n (X ^ (m * (m + 1) / 2) * ((1 + X) * invOneSub) ^ m)

/-- `A003056(k)`: largest `m` with `m * (m + 1) / 2 ≤ k`. -/
def A003056 (k : ℕ) : ℕ := (Nat.sqrt (1 + 8 * k) - 1) / 2

/-- `A142978(n, k)`: `∑_{i=0}^{n-1} C(n - 1, i) * C(k + i, n)`. -/
def A142978 (n k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, (Nat.choose (n - 1) i : ℤ) * (Nat.choose (k + i) n : ℤ)

/-- `b(n) = ∑_{k=1}^{n} A142978(n - k + 1, A003056(k))` (with `b(0) = 0`). -/
def b (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 n, A142978 (n - k + 1) (A003056 k)

theorem main : ∀ n : ℕ, 1 ≤ n → a n = b n - b (n - 2) := by
  sorry

end OMA.S_oeis_a369425

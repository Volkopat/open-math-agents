import Mathlib

/-!
# A105565: five Fibonacci numbers with n digits

Source: https://oeis.org/A105565

`a(n) = 1` if exactly five Fibonacci numbers have exactly `n` digits, and `0` otherwise.
With the partial sums `S(n) = sum_{k=1..n} a(k)`, the OEIS conjecture is

    beta - 2 < S(n) - alpha * n < beta - 1,

where `alpha = log 10 / log phi - 4` and `beta = log 5 / (2 * log phi) - 1`, `phi` the golden
ratio: each step of `n` adds `log 10 / log phi` digits' worth of Fibonacci indices, and the
bounds express that `S(n)` stays within one index of its linear trend.

Conventions: offset 1, as in the OEIS b-file. The count of indices is taken over the range
`[0, 5 * n + 10)`, a safe cutoff since `Nat.fib` grows like `phi ^ k`, so no index beyond it can
have `n` digits for `n >= 1`.
-/

namespace OMA.S_oeis_a105565

open Nat Finset Real

/-- `a(n) = 1` if exactly five Fibonacci numbers have exactly `n` digits, else `0`. -/
def a (n : ℕ) : ℕ :=
  if n > 0 then
    let lowerBound : ℕ := 10 ^ (n - 1)
    let upperBound : ℕ := 10 ^ n
    let maxK : ℕ := 5 * n + 10
    let count : ℕ :=
      (filter (fun k => lowerBound ≤ Nat.fib k ∧ Nat.fib k < upperBound) (range maxK)).card
    if count = 5 then 1 else 0
  else
    0

/-- The golden ratio `phi = (1 + sqrt 5) / 2`. -/
noncomputable def phi : ℝ := Real.goldenRatio

/-- The constant `alpha = log 10 / log phi - 4`. -/
noncomputable def alphaConst : ℝ := Real.log 10 / Real.log phi - 4

/-- The constant `beta = log 5 / (2 * log phi) - 1`. -/
noncomputable def betaConst : ℝ := Real.log 5 / (2 * Real.log phi) - 1

/-- The partial sum `S(n) = sum_{k=1..n} a(k)`. -/
noncomputable def s (n : ℕ) : ℝ :=
  (Icc 1 n).sum (fun k => (a k : ℝ))

/-- OEIS A105565: `beta - 2 < S(n) - alpha * n < beta - 1` for every `n >= 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      betaConst - 2 < s n - alphaConst * (n : ℝ) ∧
        s n - alphaConst * (n : ℝ) < betaConst - 1 := by
  sorry

end OMA.S_oeis_a105565

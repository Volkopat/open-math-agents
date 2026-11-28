import Mathlib

/-!
# OEIS A019294: iterations of `σ` needed to reach a multiple of `n`

Source: https://oeis.org/A019294
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number (`> 0`) of iterations of `σ` (sum of divisors) needed to reach a multiple of
`n` when starting from `n`. Conjectures (OEIS entry): `a(n)` is finite for every `n`, and
`lim_{n → ∞} log(∑_{k=1}^{n} a(k)) / log n = C = 1.6…`.

Conventions:
* `n ≥ 1`. Finiteness: some `m ≥ 1` has `n ∣ σ^[m](n)`; then `a(n)` is the least such `m`.
* `C = 1.6…` is read as `1.6 ≤ C < 1.7`. `main` states both conjectures.
-/

namespace OMA.S_oeis_a019294

open Filter Topology ArithmeticFunction

/-- `a(n)`: least `m ≥ 1` with `n ∣ σ^[m](n)` (`0` if there is none). -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ n ∣ (fun k => ArithmeticFunction.sigma 1 k)^[m] n}

/-- Finiteness for all `n ≥ 1`, and the growth exponent `1.6…` of the partial sums. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 1 ≤ m ∧ n ∣ (fun k => ArithmeticFunction.sigma 1 k)^[m] n) ∧
    (∃ C : ℝ, 1.6 ≤ C ∧ C < 1.7 ∧
      Tendsto (fun n : ℕ => Real.log (∑ k ∈ Finset.Icc 1 n, (a k : ℝ)) / Real.log n) atTop
        (𝓝 C)) := by
  sorry

end OMA.S_oeis_a019294

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a382124

/-- Sum of divisors `σ(n)` (OEIS A000203). -/
def sigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

/-- Coefficient sequence of `exp(∑_{k ≥ 1} u(k) * x^k / k)` defined via the logarithmic derivative
recurrence `a(0) = 1`, `a(n + 1) = (1 / (n + 1)) * ∑_{k = 1}^{n + 1} u(k) * a(n + 1 - k)`. -/
def expLogSeq (u : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
    (∑ k ∈ Finset.range (n + 1), u (k + 1) * expLogSeq u (n - k)) / ((n + 1 : ℕ) : ℚ)

/-- OEIS A382124: g.f. `A(x) = exp(∑_{n ≥ 1} (σ(n) * σ(2n) / 3) * x^n / n)`. -/
def a382124 (n : ℕ) : ℚ :=
  expLogSeq (fun k => ((sigma k * sigma (2 * k) : ℕ) : ℚ) / 3) n

/-- OEIS A382125: g.f. `B(x) = exp(∑_{n ≥ 1} σ(n) * σ(2n) * x^n / n)`. -/
def a382125 (n : ℕ) : ℚ :=
  expLogSeq (fun k => ((sigma k * sigma (2 * k) : ℕ) : ℚ)) n

/-- OEIS A382124 conjecture: for all `n ≥ 0`, `A382124(n)` and `A382125(3n)` are integers
satisfying `A382124(n) ≡ A382125(3n) (mod 3)`. -/
theorem main :
    ∀ n : ℕ,
      (a382124 n).den = 1 ∧ (a382125 (3 * n)).den = 1 ∧
      (a382124 n).num % 3 = (a382125 (3 * n)).num % 3 := by
  sorry

end OMA.S_oeis_a382124

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OMA.S_oeis_a301311

/-- OEIS A301311: G.f. `∑_{n ≥ 0} 2^n * (1 - x)^(-n^2) / 3^(n + 1)`.
Its `m`-th coefficient (for `m ≥ 1`) is `∑_{n ≥ 0} 2^n * C(n^2 + m - 1, m) / 3^(n + 1)`.
Conjecture: `a(m)` is divisible by `10` for all `m > 0`. -/
theorem main :
    ∀ m : ℕ, 1 ≤ m →
      ∃ k : ℕ, HasSum (fun n : ℕ => (2 : ℝ) ^ n * (Nat.choose (n ^ 2 + m - 1) m : ℝ) / (3 : ℝ) ^ (n + 1))
        ((10 * k : ℕ) : ℝ) := by
  sorry

end OMA.S_oeis_a301311

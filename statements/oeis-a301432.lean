import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OMA.S_oeis_a301432

/-- OEIS A301432: G.f. `∑_{n ≥ 0} 3^n * (1 + x)^(n^2) / 4^(n + 1)`.
Its `m`-th coefficient is `∑_{n ≥ 0} 3^n * C(n^2, m) / 4^(n + 1)`.
Conjecture: `a(m)` is divisible by `21` for all `m > 0`. -/
theorem main :
    ∀ m : ℕ, 1 ≤ m →
      ∃ k : ℕ, HasSum (fun n : ℕ => (3 : ℝ) ^ n * (Nat.choose (n ^ 2) m : ℝ) / (4 : ℝ) ^ (n + 1))
        ((21 * k : ℕ) : ℝ) := by
  sorry

end OMA.S_oeis_a301432

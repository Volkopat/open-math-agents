import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Bounds.Defs

/-!
# OEIS A343087

For each positive index n, the conjecture says that the least prime p
with τ(p - 1) = 2^n is also the least integer m ≥ 2 with
τ(m - 1) = τ(m)^n. Here τ counts positive divisors.
Source: https://oeis.org/A343087
-/

namespace OMA.S_oeis_a343087

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ,
      IsLeast {q : ℕ | q.Prime ∧ (q - 1).divisors.card = 2 ^ n} p ∧
      IsLeast {m : ℕ | 2 ≤ m ∧ (m - 1).divisors.card = m.divisors.card ^ n} p := by
  sorry

end OMA.S_oeis_a343087

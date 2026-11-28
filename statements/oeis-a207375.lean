import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finset.Max

namespace OMA.S_oeis_a207375

/-- Lower central divisor of `n` (largest divisor `d ∣ n` with `d^2 ≤ n`, `0` if `n = 0`). -/
def lowerCentral (n : ℕ) : ℕ :=
  ((n.divisors.filter (fun d => d * d ≤ n)).max).getD 0

/-- Upper central divisor of `n` (smallest divisor `d ∣ n` with `n ≤ d^2`, `0` if `n = 0`). -/
def upperCentral (n : ℕ) : ℕ :=
  ((n.divisors.filter (fun d => n ≤ d * d)).min).getD 0

/-- OEIS A207375 Conjecture 1: in the irregular array of central divisors of `n ≥ 1`,
every row `n` has maximum entry `upperCentral n`, the lower central divisor never sets a
strict record for `n ≥ 2`, and `upperCentral n` sets a strict record (strictly exceeding
all entries in rows `1 ≤ m < n`) if and only if `n = 1` or `n` is prime (i.e., `n ∈ A008578`). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → lowerCentral n ≤ upperCentral n) ∧
    (∀ n : ℕ, 2 ≤ n → ∃ m : ℕ, 1 ≤ m ∧ m < n ∧ lowerCentral n ≤ upperCentral m) ∧
    (∀ n : ℕ, 1 ≤ n →
      ((∀ m : ℕ, 1 ≤ m → m < n → upperCentral m < upperCentral n) ↔ (n = 1 ∨ n.Prime))) := by
  sorry

end OMA.S_oeis_a207375

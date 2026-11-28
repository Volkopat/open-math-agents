import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.NumberTheory.Divisors

/- Franklin T. Adams-Watters, OEIS A047968, April 19, 2014.
The sum of ordinary partition numbers over divisors is strictly increasing
from index seven onward. -/
namespace OMA.S_oeis_a047968

theorem main : ∀ m n : ℕ, 7 ≤ m → m < n →
    (∑ d ∈ m.divisors, Fintype.card (Nat.Partition d)) <
      ∑ d ∈ n.divisors, Fintype.card (Nat.Partition d) := by sorry

end OMA.S_oeis_a047968

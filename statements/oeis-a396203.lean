import Mathlib

/-!
# A396203: Primes whose next-prime gap is the floor of their binary logarithm

Source: https://oeis.org/A396203
Credit: @gblacher2
-/

namespace OMA.S_oeis_a396203

/-- Infinitely many primes `p` have next prime `q` at distance `Nat.log2 p`.
The interval condition says that `q` is the immediate successor of `p` among primes. -/
theorem main :
    {p : ℕ | p.Prime ∧ ∃ q : ℕ, q.Prime ∧ p < q ∧ q - p = p.log2 ∧
      ∀ r : ℕ, p < r → r < q → ¬ r.Prime}.Infinite := by
  sorry

end OMA.S_oeis_a396203

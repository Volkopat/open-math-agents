import Mathlib

/-!
# OEIS A398563

Source: https://oeis.org/A398563
Credit: @cheniverse

Michael Shmoish's entry states that finiteness of the twin prime pairs implies
finiteness of the semiprimes that are differences of two prime cubes. Each
twin pair is indexed by its smaller prime. A semiprime counts prime factors
with multiplicity, so squares of primes are included.
-/

namespace OMA.S_oeis_a398563

theorem main :
    {r : ℕ | r.Prime ∧ (r + 2).Prime}.Finite →
    {n : ℕ | Nat.IsSemiprime n ∧
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ q < p ∧ n = p ^ 3 - q ^ 3}.Finite := by
  sorry

end OMA.S_oeis_a398563

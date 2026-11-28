import Mathlib

/-!
# OEIS A377808

Michel Lagneau (8 November 2024) asks whether infinitely many primes `p` admit a cut of
`1, …, p` into consecutive nonempty blocks with equal totients of their sums.
Source: https://oeis.org/A377808
-/

namespace OMA.S_oeis_a377808

theorem main :
    {p : ℕ | p.Prime ∧ ∃ N : ℕ, 0 < N ∧ N < p ∧
      Nat.totient (∑ i ∈ Finset.Icc 1 N, i) =
        Nat.totient (∑ i ∈ Finset.Ioc N p, i)}.Infinite := by
  sorry

end OMA.S_oeis_a377808

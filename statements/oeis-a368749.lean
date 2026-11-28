import Mathlib

/-!
# OEIS A368749

Source: https://oeis.org/A368749
Credit: @cheniverse

The OEIS comment asks whether the number of integers that are not prime powers
between consecutive primes is unbounded. For every natural bound, some gap
contains at least that many such integers. The definition of an individual
sequence term uses an exact count.

This bound also follows from falagar's 2010 construction of arbitrarily long
blocks in which each integer has at least two distinct prime factors.
https://mathoverflow.net/a/35364
-/

namespace OMA.S_oeis_a368749

theorem main :
    ∀ bound : ℕ, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧
      (∀ r : ℕ, p < r → r < q → ¬ r.Prime) ∧
      bound ≤ ((Finset.Ioo p q).filter (fun n : ℕ => ¬ IsPrimePow n)).card := by
  sorry

end OMA.S_oeis_a368749

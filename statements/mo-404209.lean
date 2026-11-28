import Mathlib

/-!
# An even base with infinitely many generalized Fermat primes

Source: https://mathoverflow.net/questions/404209/is-there-an-even-number-a-such-that-a2n1-is-prime-for-infinitely-many
Credit: @shc261392

Question. Is there an even number `a` such that `a^(2^n) + 1` is prime for infinitely many `n`?

Reading used here: the affirmative answer, with `a` a positive even natural number.
-/

namespace OMA.S_mo_404209

theorem main : ∃ a : ℕ, 0 < a ∧ Even a ∧ {n : ℕ | (a ^ 2 ^ n + 1).Prime}.Infinite := by
  sorry

end OMA.S_mo_404209

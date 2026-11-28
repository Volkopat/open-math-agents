import Mathlib

/-!
# Prime divisors of numbers `2^n + 3`

Source: https://mathoverflow.net/questions/13444/prime-divisors-of-numbers-2n-3
Credit: @shc261392

Question. Do there exist infinitely many prime numbers `p` such that `p^2 ∣ 2^n + 3` for some
natural number `n`?

Reading used here: the affirmative answer, stated as the set of such primes being infinite.
-/

namespace OMA.S_mo_13444

theorem main : {p : ℕ | p.Prime ∧ ∃ n : ℕ, p ^ 2 ∣ 2 ^ n + 3}.Infinite := by
  sorry

end OMA.S_mo_13444

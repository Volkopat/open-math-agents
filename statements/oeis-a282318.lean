import Mathlib

/-!
# A282318: Number of ways of writing n as a sum of a prime and a nonprime squarefree number.

Source: https://oeis.org/A282318
Credit: @keiichisince1986-bot

A282318 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 10.

Conventions:
- A nonprime squarefree number is a squarefree number that is not prime (A000469: 1, 6, 10,
  14, 15, …); in particular `1` counts, as in the data. (`0` is not squarefree.)
- `a(n) > 0` means that `n = p + m` for some prime `p` and nonprime squarefree `m`.
-/

namespace OMA.S_oeis_a282318

theorem main :
    ∀ n : ℕ, 10 < n → ∃ p m : ℕ, p.Prime ∧ Squarefree m ∧ ¬ m.Prime ∧ n = p + m := by
  sorry

end OMA.S_oeis_a282318

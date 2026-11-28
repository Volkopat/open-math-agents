import Mathlib

/-!
# A266952: Least prime p such that p-2 and 6n-p and 6n+2-p are also prime, or 0 if no such prime exists.

Source: https://oeis.org/A266952
Credit: @keiichisince1986-bot

A266952 is the sequence `a(n)` named in the title. The entry states:
Up to 10^5, the only indices for which a(n)=0 are {0, 1, 16, 67, 86, 131, 151, 186, 191, 211, 226,
541, 701}. I conjecture that this list is finite, and probably complete.

Conventions:
- `a(n) = 0` means that no prime `p` has `p - 2`, `6n - p` and `6n + 2 - p` all prime. Natural-number
  truncation is harmless: a truncated value is `0`, which is not prime.
- We formalize the stated conjecture, that the set of indices with `a(n) = 0` is finite; the list above
  is its conjectured complete value (a direct computation confirms it below `2 · 10^4`).
-/

namespace OMA.S_oeis_a266952

theorem main :
    {n : ℕ | ¬ ∃ p : ℕ, p.Prime ∧ (p - 2).Prime ∧ (6 * n - p).Prime ∧ (6 * n + 2 - p).Prime}.Finite := by
  sorry

end OMA.S_oeis_a266952

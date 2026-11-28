import Mathlib

/-!
# OEIS A090698: primes of the form 2*n^2+1

Source: https://oeis.org/A090698 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

The sequence lists the primes of the form `2*n^2+1` (3, 19, 73, 163, 883, ...). The entry records
the comment:

  Conjecture: 2^(a(n)-1) - 3 is not prime. - Vincenzo Librandi, Feb 04 2013.

We formalize this conjecture: for every prime `p` of the form `2*n^2+1` (with `n` a natural
number), the number `2^(p-1) - 3` is not prime. Since every such prime is at least `3`, the
natural-number subtraction is exact.
-/

namespace OMA.S_oeis_a090698

/-- Membership in A090698: `p` is a prime of the form `2*n^2+1`. -/
def InSeq (p : ℕ) : Prop := p.Prime ∧ ∃ n : ℕ, p = 2 * n ^ 2 + 1

/-- Librandi's conjecture: `2^(p-1) - 3` is never prime for a term `p` of A090698. -/
theorem main : ∀ p : ℕ, InSeq p → ¬ (2 ^ (p - 1) - 3).Prime := by
  sorry

end OMA.S_oeis_a090698

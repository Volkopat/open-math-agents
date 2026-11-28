import Mathlib

/-!
# A267944: Primes that are a prime power minus two.

Source: https://oeis.org/A267944
Credit: @keiichisince1986-bot

A267944 is the sequence `a(n)` named in the title. The entry states:
The generalized Bunyakovsky conjecture implies that for every k there are infinitely many terms of
the form p^k - 2. - Robert Israel, Jan 22 2016 (The statement below is this claim, unconditionally.)

Conventions:
- A term of the form `p^k - 2` is a prime `q` with `q + 2 = p^k` for a prime `p`. For `k = 1` this is the twin
  prime conjecture.
-/

namespace OMA.S_oeis_a267944

theorem main :
    ∀ k : ℕ, 1 ≤ k → {q : ℕ | q.Prime ∧ ∃ p : ℕ, p.Prime ∧ q + 2 = p ^ k}.Infinite := by
  sorry

end OMA.S_oeis_a267944

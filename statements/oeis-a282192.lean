import Mathlib

/-!
# A282192: Number of ways of writing n as a sum of a prime and a squarefree semiprime.

Source: https://oeis.org/A282192
Credit: @keiichisince1986-bot

A282192 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 30.

Conventions:
- A squarefree semiprime is a product of two distinct primes (A006881: 6, 10, 14, 15, …): a
  squarefree number whose prime factorization has length `2`.
- `a(n) > 0` means that `n = p + m` for some prime `p` and squarefree semiprime `m`.
-/

namespace OMA.S_oeis_a282192

/-- `m` is a product of two distinct primes. -/
def IsSquarefreeSemiprime (m : ℕ) : Prop :=
  Squarefree m ∧ m.primeFactorsList.length = 2

theorem main :
    ∀ n : ℕ, 30 < n → ∃ p m : ℕ, p.Prime ∧ IsSquarefreeSemiprime m ∧ n = p + m := by
  sorry

end OMA.S_oeis_a282192

import Mathlib

/-!
# A141170: the primes x^2 + 4xy - 2y^2 are the primes of both forms x^2 + 2y^2 and x^2 + 3y^2

Source: https://oeis.org/A141170 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A141170, offset 1:
Primes of the form x^2+4*x*y-2*y^2 (as well as of the form 3*x^2+6*x*y+y^2). Data
3, 19, 43, 67, 73, 97, 139, 163, 193, 211, 241, 283, 307, 313, 331, 337, 379, 409, 433, ...

Comments: Conjecture: this is also the list of primes that are simultaneously of the form
x^2+2y^2 and of the form x^2+3y^2; that is, the intersection of A002476 and A033203.
- Zak Seidov, Jun 07 2014

Formalization notes.
* The variables x, y of the quadratic forms are integers (the form x^2 + 4xy - 2y^2 is
  indefinite, and the entry gives it also as u^2 - 6v^2 with u = x + 2y, v = y).
* `main` states the conjecture in its first wording: a prime p is of the form
  x^2 + 4xy - 2y^2 if and only if p is of the form a^2 + 2b^2 and of the form c^2 + 3d^2.
* The second wording (the intersection of A002476, the primes 6m + 1, and A033203) differs
  from the first only at the prime 3: 3 = 1 + 4 - 2 = 1 + 2 = 0 + 3 is a term of A141170 and
  has both forms, but 3 is not of the form 6m + 1. For all other primes p, p = c^2 + 3d^2 holds
  if and only if p = 6m + 1.
-/

namespace OMA.S_oeis_a141170

/-- Seidov's conjecture: a prime p is of the form x^2 + 4xy - 2y^2 if and only if p is of the
form a^2 + 2b^2 and of the form c^2 + 3d^2. -/
theorem main : ∀ p : ℕ, p.Prime →
    ((∃ x y : ℤ, (p : ℤ) = x ^ 2 + 4 * x * y - 2 * y ^ 2) ↔
      ((∃ a b : ℤ, (p : ℤ) = a ^ 2 + 2 * b ^ 2) ∧ (∃ c d : ℤ, (p : ℤ) = c ^ 2 + 3 * d ^ 2))) := by
  sorry

end OMA.S_oeis_a141170

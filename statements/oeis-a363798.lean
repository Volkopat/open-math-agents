import Mathlib

/-!
# OEIS A363798: every term is (q^2-1)/2 + j(q^2-q) with q an odd prime and q^k + 2k not prime

Source: https://oeis.org/A363798 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Israel, Jun 23 2023), offset 1: Numbers k such that there is no prime p for which
p^k + 2*k is prime. Comment: Includes k = (q^2-1)/2 + j*(q^2-q) for odd primes q and nonnegative
integers j such that q^k + 2*k is not prime, since for primes p <> q we have q | p^k + 2*k.
Conjecture: all terms are of this form. Data: 12, 16, 22, 24, 28, 32, 40, 46, ...

Formalization notes:
* IsTerm k says that no prime p makes p ^ k + 2 * k prime. The terms are positive integers (the
  list starts at 12; k = 0 would satisfy the condition vacuously, since p ^ 0 = 1), so main is
  stated for k ≥ 1.
* IsForm k is the comment's form word for word: k = (q^2 - 1)/2 + j * (q^2 - q) for a prime
  q ≠ 2 and a natural number j, with q ^ k + 2 * k not prime. The subtractions and the division
  are exact in ℕ because q ≥ 3 is odd.
* main says: every term k ≥ 1 is of this form.
* Controls proved in the proof file: 12 is a term and has the form (q = 5, j = 0).
-/

namespace OMA.S_oeis_a363798

/-- `k` is a term: no prime `p` makes `p ^ k + 2 * k` prime. -/
def IsTerm (k : ℕ) : Prop := ∀ p : ℕ, p.Prime → ¬ (p ^ k + 2 * k).Prime

/-- Israel's form: `k = (q^2 - 1)/2 + j * (q^2 - q)` for an odd prime `q` and a natural number `j`,
with `q ^ k + 2 * k` not prime. -/
def IsForm (k : ℕ) : Prop :=
  ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ ∃ j : ℕ, k = (q ^ 2 - 1) / 2 + j * (q ^ 2 - q) ∧ ¬ (q ^ k + 2 * k).Prime

/-- Israel's conjecture: all terms are of this form. -/
theorem main : ∀ k : ℕ, 1 ≤ k → IsTerm k → IsForm k := by
  sorry

end OMA.S_oeis_a363798

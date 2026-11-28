import Mathlib

/-!
# A189045: Semiprimes which are sub-perfect powers.

Source: https://oeis.org/A189045
Credit: @agchua

Comments of A189045:
  Numbers of the form p*q where p and q are primes, not necessarily distinct, such that p*q + 1 is a
  perfect power (squares, cubes, etc.).
  By Catalan's conjecture (or now Mihailescu's theorem), p and q are always distinct.
  - T. D. Noe, Apr 15 2011
IsTerm n says that n is a term: n = p*q with p and q prime, and n + 1 = m^k for some m and some
k >= 2 (a perfect power, as in A001597; the formula of the entry is A001358 INTERSECTION
{A001597 - 1}). The claim of the second comment is stated: whenever a term is written as p*q with
p and q prime, p and q are distinct. This gives the listed terms 15, 26, 35, 143, 215, 323, ...
-/

namespace OMA.S_oeis_a189045

/-- n is a term of A189045: a semiprime p*q such that n + 1 is a perfect power m^k, k >= 2. -/
def IsTerm (n : ℕ) : Prop :=
  (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q) ∧ ∃ m k : ℕ, 2 ≤ k ∧ n + 1 = m ^ k

/-- For every term n = p*q of A189045 with p and q prime, p and q are distinct. -/
theorem main : ∀ n p q : ℕ, IsTerm n → p.Prime → q.Prime → n = p * q → p ≠ q := by
  sorry

end OMA.S_oeis_a189045

import Mathlib

/-!
# A129807: Primes congruent to +-7 mod 18.

Source: https://oeis.org/A129807
Credit: @agchua

Formula line of A129807 (conjecture by R. J. Mathar, Jun 10 2007):
  Conjecture: Equals (A061241 UNION A061238) MINUS {2}.
Offset 1, data 7, 11, 29, 43, 47, 61, 79, 83, 97, 101, ... A prime p is congruent to +7 or to -7
modulo 18 exactly when p mod 18 is 7 or 11. The other sequences, from their name lines:
  A061241: Prime numbers == 7 (mod 9).
  A061238: Prime numbers == 2 (mod 9).
The conjecture says that a natural number is a term of A129807 if and only if it is a term of
A061241 or of A061238 and is not 2.
-/

namespace OMA.S_oeis_a129807

/-- p is a term of A129807: a prime congruent to 7 or to -7 (that is, 11) modulo 18. -/
def IsTerm (p : ℕ) : Prop := p.Prime ∧ (p % 18 = 7 ∨ p % 18 = 11)

/-- p is a term of A061241: a prime congruent to 7 modulo 9. -/
def InA061241 (p : ℕ) : Prop := p.Prime ∧ p % 9 = 7

/-- p is a term of A061238: a prime congruent to 2 modulo 9. -/
def InA061238 (p : ℕ) : Prop := p.Prime ∧ p % 9 = 2

/-- The conjecture: A129807 = (A061241 union A061238) minus {2}. -/
theorem main : ∀ p : ℕ, IsTerm p ↔ ((InA061241 p ∨ InA061238 p) ∧ p ≠ 2) := by
  sorry

end OMA.S_oeis_a129807

import Mathlib

/-!
# A240920: Prime numbers that occur as divisors of numbers of the form m^2 + 5.

Source: https://oeis.org/A240920
Credit: @agchua

Comment of A240920 (the entry is by J. Lowell, Aug 02 2014):
  Conjecture: a prime number is in this sequence if and only if its next-to-last digit is even.
Offset 1, first terms 2, 3, 5, 7, 23, 29, 41, 43, 47, 61. A prime p is a term iff p divides
m^2 + 5 for some natural number m. The next-to-last (tens) digit of p in base 10 is
(p / 10) mod 10; for a one-digit prime it is read as 0. The conjecture is stated for every
prime p. The entry records that Jens Kruse Andersen (Aug 09 2014) proved it by quadratic
reciprocity.
-/

namespace OMA.S_oeis_a240920

/-- p is a term of A240920: a prime that divides m^2 + 5 for some m. -/
def IsTerm (p : ℕ) : Prop := p.Prime ∧ ∃ m : ℕ, p ∣ m ^ 2 + 5

/-- The conjecture: a prime p is a term iff its next-to-last decimal digit is even. -/
theorem main : ∀ p : ℕ, p.Prime → (IsTerm p ↔ Even (p / 10 % 10)) := by
  sorry

end OMA.S_oeis_a240920

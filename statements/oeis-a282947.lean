import Mathlib

/-!
# A282947: Number of ways of writing n as a sum of a perfect power and a squarefree semiprime.

Source: https://oeis.org/A282947
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A282947 (Ilya Gutkovskiy, Feb 25 2017):
a(n) > 0 for all n > 108.

Conventions:
* The sequence has offset 0 (data 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 2, 2, ...).
  `a n` is the number of pairs (x, y) of natural numbers with x + y = n, x a perfect power and
  y a squarefree semiprime (the coefficient of x^n in the product of the two generating
  functions in the FORMULA section).
* Perfect powers are the terms of A001597: 1, 4, 8, 9, 16, 25, 27, ..., i.e. the numbers m^k
  with m >= 1 and k >= 2 (so 1 is a perfect power and 0 is not).
* Squarefree semiprimes are the terms of A006881: products p*q of two distinct primes,
  rendered with p < q.
* Only the first conjecture of the entry (a(n) > 0 for n > 108) is formalized.
-/

namespace OMA.S_oeis_a282947

/-- Perfect powers (A001597): m^k with m >= 1, k >= 2. -/
def IsPerfectPower (x : ℕ) : Prop := ∃ m k : ℕ, 1 ≤ m ∧ 2 ≤ k ∧ m ^ k = x

/-- Squarefree semiprimes (A006881): products of two distinct primes. -/
def IsSquarefreeSemiprime (y : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ y = p * q

/-- A282947: number of ways of writing n as a perfect power plus a squarefree semiprime. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ | x.1 + x.2 = n ∧ IsPerfectPower x.1 ∧ IsSquarefreeSemiprime x.2}

/-- The conjecture: a(n) > 0 for all n > 108. -/
theorem main : ∀ n : ℕ, 108 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a282947

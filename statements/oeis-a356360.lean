import Mathlib

/-!
# A356360: Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(n+1))))).

Source: https://oeis.org/A356360
Credit: @agchua

Comment of A356360 (unsigned; the entry is by Mohammed Bouras, Oct 15 2022):
  Conjecture: The sequence contains only 1's and the primes.
Formula line of A356360 (unsigned):
  From the conjecture: Except for n = 5, a(n)= 2n - 1 if 2n-1 is prime, 1 otherwise.
The sequence has offset 3. For n ≥ 3 the continued fraction has the levels j = 2, 3, ..., n - 1,
each of the form j - (j+1)/(...), and n + 1 at the bottom; n = 3 gives 1/(2 - 3/4) = 4/5, so
a(3) = 5, as in the data. The fraction is evaluated in ℚ and a(n) is the denominator of the
result in lowest terms. main states the comment's conjecture and the formula line, both for
every n ≥ 3 (the offset).
-/

namespace OMA.S_oeis_a356360

/-- The continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(n+1))))): the levels j = 2, ..., n - 1
are folded from the bottom, starting from n + 1. -/
def cf (n : ℕ) : ℚ :=
  1 / (List.range' 2 (n - 2)).foldr (fun j x => (j : ℚ) - ((j : ℚ) + 1) / x) ((n : ℚ) + 1)

/-- A356360(n): the denominator of cf n. -/
def a (n : ℕ) : ℕ := (cf n).den

/-- The comment's conjecture (every term is 1 or a prime) and the formula line (for n ≠ 5,
a(n) = 2n - 1 if 2n - 1 is prime and a(n) = 1 otherwise), for n ≥ 3. -/
theorem main : (∀ n : ℕ, 3 ≤ n → a n = 1 ∨ (a n).Prime) ∧
    (∀ n : ℕ, 3 ≤ n → n ≠ 5 →
      ((2 * n - 1).Prime → a n = 2 * n - 1) ∧ (¬ (2 * n - 1).Prime → a n = 1)) := by
  sorry

end OMA.S_oeis_a356360

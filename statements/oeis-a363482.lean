import Mathlib

/-!
# A363482: the denominators of 1/(2-3/(3-4/(4-5/(...(n-1)-n/(-5))))) are 1 or prime, except 49

Source: https://oeis.org/A363482 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A363482, offset 3:
Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(-5))))). Data
13, 23, 7, 49, 13, 83, 103, 5, 149, 1, 29, 233, 53, 23, 67, 373, 59, 1, 499, 109, 593, ...

Comments:
Conjecture: Except for 49, every term of this sequence is either a prime or 1.
The conjecture holds through n=10000. The set of ordered primes appear to match A038901.
- Bill McEachen, Jul 08 2025

Formalization notes.
* `nest j y` is the expression 2 - 3/(3 - 4/(... ((j+1) - (j+2)/y))) with j levels, as a
  rational number: one more level replaces the innermost y by (j+2) - (j+3)/y. The continued
  fraction of the entry is 1 / nest (n-2) (-5); for n = 3 this is 1/(2 - 3/(-5)).
* `a n` is the denominator (`Rat.den`, the positive denominator in lowest terms). The values
  a(3), ..., a(23) agree with the data.
* No division by zero occurs in the continued fraction: the innermost value (n-1) + n/5 is
  positive, and the other inner values k - (k+1)/(...) are at least k - 2 for k >= 3. Thus the
  division of ℚ in Lean (with x/0 = 0) gives the true value.
* `main` states the conjecture for all n >= 3: if a(n) is not 49 then a(n) is 1 or a prime.
  The term 49 occurs at n = 6. The remark on A038901 is an observation and is not stated here.
-/

namespace OMA.S_oeis_a363482

/-- `nest j y` is the expression 2 - 3/(3 - 4/(4 - ... ((j+1) - (j+2)/y))) with `j` levels:
`nest 0 y = y`, `nest 1 y = 2 - 3/y`, `nest 2 y = 2 - 3/(3 - 4/y)`, and so on. -/
def nest : ℕ → ℚ → ℚ
  | 0, y => y
  | j + 1, y => nest j ((j + 2 : ℚ) - (j + 3 : ℚ) / y)

/-- A363482(n), n ≥ 3: the denominator of 1/(2 - 3/(3 - 4/(4 - ... ((n-1) - n/(-5))))). -/
def a (n : ℕ) : ℕ := (1 / nest (n - 2) (-5 : ℚ)).den

/-- Except for 49, every term of the sequence is either a prime or 1. -/
theorem main : ∀ n : ℕ, 3 ≤ n → a n ≠ 49 → a n = 1 ∨ (a n).Prime := by
  sorry

end OMA.S_oeis_a363482

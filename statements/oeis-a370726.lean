import Mathlib

/-!
# A370726: the denominators of 1/(2-3/(3-4/(4-5/(...(n-1)-n/(n+3))))) are 1 or prime

Source: https://oeis.org/A370726 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A370726, offset 3:
Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(n+3))))). Data
3, 13, 17, 7, 5, 29, 11, 37, 41, 1, 7, 53, 19, 61, 1, 23, 73, 1, 1, 1, 89, 31, 97, 101, 1, ...

Comments:
Conjecture: The sequence contains only 1's and the primes.
Conjecture: Record values correspond to A002144 (n>3). - Bill McEachen, May 21 2024

Formalization notes.
* `nest j y` is the expression 2 - 3/(3 - 4/(... ((j+1) - (j+2)/y))) with j levels, as a
  rational number: one more level replaces the innermost y by (j+2) - (j+3)/y. The continued
  fraction of the entry is 1 / nest (n-2) (n+3); for n = 3 this is 1/(2 - 3/6) = 2/3.
* `a n` is the denominator (`Rat.den`, the positive denominator in lowest terms). The values
  a(3), ..., a(27) agree with the data.
* No division by zero occurs in the continued fraction: the inner values
  k - (k+1)/(...) are at least k - 2 for k >= 3. Thus the division of ℚ in Lean (with x/0 = 0)
  gives the true value.
* `main` states the first conjecture for all n >= 3. The second conjecture (on the record
  values) is not stated here.
-/

namespace OMA.S_oeis_a370726

/-- `nest j y` is the expression 2 - 3/(3 - 4/(4 - ... ((j+1) - (j+2)/y))) with `j` levels:
`nest 0 y = y`, `nest 1 y = 2 - 3/y`, `nest 2 y = 2 - 3/(3 - 4/y)`, and so on. -/
def nest : ℕ → ℚ → ℚ
  | 0, y => y
  | j + 1, y => nest j ((j + 2 : ℚ) - (j + 3 : ℚ) / y)

/-- A370726(n), n ≥ 3: the denominator of 1/(2 - 3/(3 - 4/(4 - ... ((n-1) - n/(n+3))))). -/
def a (n : ℕ) : ℕ := (1 / nest (n - 2) ((n : ℚ) + 3)).den

/-- The sequence contains only 1's and primes. -/
theorem main : ∀ n : ℕ, 3 ≤ n → a n = 1 ∨ (a n).Prime := by
  sorry

end OMA.S_oeis_a370726

import Mathlib

/-!
# A362086: the denominators of 1/(2-3/(3-4/(4-5/(...(n-1)-n/(-3))))) are 1 or prime, except 9

Source: https://oeis.org/A362086 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A362086, offset 3:
Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(-3))))). Data
3, 17, 9, 13, 53, 23, 29, 107, 43, 17, 179, 23, 79, 269, 101, 113, 29, 139, 1, 503, 61, ...

Comments:
Conjecture: Except for 9, every term of this sequence is either a prime or 1.
Conjecture: Record values correspond to A248697 (n>3). - Bill McEachen, Mar 06 2024

Formalization notes.
* `nest j y` is the expression 2 - 3/(3 - 4/(... ((j+1) - (j+2)/y))) with j levels, as a
  rational number: one more level replaces the innermost y by (j+2) - (j+3)/y. The continued
  fraction of the entry is 1 / nest (n-2) (-3); for n = 3 this is 1/(2 - 3/(-3)).
* `a n` is the denominator (`Rat.den`, the positive denominator in lowest terms). The values
  a(3), ..., a(23) agree with the data.
* No division by zero occurs in the continued fraction: the innermost value (n-1) + n/3 is
  positive, and the other inner values k - (k+1)/(...) are at least k - 2 for k >= 3. Thus the
  division of ℚ in Lean (with x/0 = 0) gives the true value.
* `main` states the first conjecture for all n >= 3: if a(n) is not 9 then a(n) is 1 or a
  prime. The term 9 occurs at n = 5. The second conjecture (on the record values) is not stated
  here.
-/

namespace OMA.S_oeis_a362086

/-- `nest j y` is the expression 2 - 3/(3 - 4/(4 - ... ((j+1) - (j+2)/y))) with `j` levels:
`nest 0 y = y`, `nest 1 y = 2 - 3/y`, `nest 2 y = 2 - 3/(3 - 4/y)`, and so on. -/
def nest : ℕ → ℚ → ℚ
  | 0, y => y
  | j + 1, y => nest j ((j + 2 : ℚ) - (j + 3 : ℚ) / y)

/-- A362086(n), n ≥ 3: the denominator of 1/(2 - 3/(3 - 4/(4 - ... ((n-1) - n/(-3))))). -/
def a (n : ℕ) : ℕ := (1 / nest (n - 2) (-3 : ℚ)).den

/-- Except for 9, every term of the sequence is either a prime or 1. -/
theorem main : ∀ n : ℕ, 3 ≤ n → a n ≠ 9 → a n = 1 ∨ (a n).Prime := by
  sorry

end OMA.S_oeis_a362086

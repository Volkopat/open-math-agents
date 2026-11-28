import Mathlib

/-!
# OEIS A249968: the squares of the terms end in 00 or 56

Source: https://oeis.org/A249968 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Chai Wah Wu, Nov 09 2014), offset 1: Numbers whose squares remain squares when prepended
with 2 and appended with 25 in base 10. Comment: Conjecture: squares of numbers in the sequence ends
in either 00 or 56. Example: 14130^2 = 199656900, 219965690025 = 469005^2.

Formalization notes:
* For m = n^2 with d decimal digits, prepending 2 and appending 25 gives 2 * 10^(d+2) + 100 m + 25;
  d is the length of `Nat.digits 10 m`, the usual digit count for m >= 1.
* The terms are positive integers (offset 1, first term 16).
* Ends in 00 or 56: the last two decimal digits, n^2 mod 100 is 0 or 56. `main` also says that
  n^2 >= 100, so that n^2 has these two digits.
* Controls from the entry (proved in the proof file by kernel computation): 16 and 14130 are terms;
  1, 2 and 3 are not.
-/

namespace OMA.S_oeis_a249968

/-- The decimal number 2, then the digits of m, then 2, 5: 2 * 10^(d+2) + 100 m + 25, where d is the
number of decimal digits of m. -/
def wrap (m : ℕ) : ℕ := 2 * 10 ^ ((Nat.digits 10 m).length + 2) + 100 * m + 25

/-- n is a term of A249968: n is positive and n^2 prepended with 2 and appended with 25 is a square. -/
def InA249968 (n : ℕ) : Prop := 0 < n ∧ IsSquare (wrap (n ^ 2))

/-- Wu's conjecture: the square of every term has at least three digits and ends in 00 or 56. -/
theorem main : ∀ n : ℕ, InA249968 n → 100 ≤ n ^ 2 ∧ (n ^ 2 % 100 = 0 ∨ n ^ 2 % 100 = 56) := by
  sorry

end OMA.S_oeis_a249968

import Mathlib

/-!
# A116649: positions where the least missing number of A116626 increases

Source: https://oeis.org/A116649 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A116649 (Antti Karttunen, Feb 21 2006), offset 1: positions where A116648(i) is greater
than A116648(i-1). Data 1, 3, 5, 9, 15, 17, 23, 25, 29, 33, 41, 49, 53, 63, 67, 71, 75, 79, ...

Comments: Equivalently, from i>1 onward those i where A116626(i) = A116648(i-1).
Conjecture: all the terms are odd.

Related entries.
* A116626 (Hanna, Karttunen): a(1)=1; a(odd n) = a(n-1) XOR a(n-2), for a(even n) we find the
  first i > 1 such that neither i nor (i XOR A116626(n-1)) is present in A116626(1..n-1), in
  which case a(n) = (i XOR A116626(n-1)). Data 1, 3, 2, 6, 4, 12, 8, 13, 5, 15, 10, 26, ...
* A116648: least natural number which does not occur in A116626(1..n). Data 2, 2, 4, 4, 5, ...

Formalization notes.
* `a` is A116626 with the convention a(0) = 0 (so that a(3) = a(2) XOR a(1) is the general
  rule and the index 0 is not used elsewhere). For an even index the first admissible i is the
  infimum (`sInf`) of the set of admissible numbers. This set is never empty, because only
  finitely many numbers are present.
* `mex n` is A116648(n): the least positive integer that is not one of a(1), ..., a(n). For
  n = 0 this gives 1, which makes 1 a term of A116649 as in the data.
* `main` is the conjecture: each position i >= 1 with A116648(i) > A116648(i-1) is odd.
-/

namespace OMA.S_oeis_a116649

/-- A116626, with `a 0 = 0`. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) =>
    if Even n then
      sInf {i : ℕ | 1 < i ∧ ∀ j : ℕ, 1 ≤ j → (h : j < n + 2) →
        a j ≠ i ∧ a j ≠ i ^^^ a (n + 1)} ^^^ a (n + 1)
    else a (n + 1) ^^^ a n

/-- A116648: the least positive integer that does not occur in a(1), ..., a(n). -/
noncomputable def mex (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ∀ j : ℕ, 1 ≤ j → j ≤ n → a j ≠ m}

/-- Conjecture of Karttunen: all terms of A116649 are odd. -/
theorem main : ∀ i : ℕ, 1 ≤ i → mex (i - 1) < mex i → Odd i := by
  sorry

end OMA.S_oeis_a116649

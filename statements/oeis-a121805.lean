import Mathlib

/-!
# A121805: The "comma sequence" is finite for every initial term

Source: https://oeis.org/A121805
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

OEIS A121805 (Eric Angelini, 2006) is the "comma sequence": the lexicographically earliest
sequence of positive numbers such that the two digits adjacent to each comma, read as a
two-digit number, equal the difference of the neighbouring terms. The entry restates the rule
explicitly (base 10): a(1) = 1, and for n > 1, with x the last digit of a(n-1),
a(n) = a(n-1) + 10*x + y, where y is the leading digit of a(n) and y is the smallest digit with
this property; if no such digit exists the sequence stops. Started at 1, it has exactly
2137453 terms (W. Edwin Clark), so that case is known. The open problem is the comment

  "Conjecture: This sequence is finite, for any initial term." (N. J. A. Sloane, Nov 14 2023)

Modelling choices:
* "Initial term" is read as running the same rule from an arbitrary positive integer `s`
  in place of a(1) = 1, as the cross-referenced sequences A139284 (start 2), A366492 (start 4),
  ..., A367354 (start 10) and A330128 / A330129 (number of terms / last term for start n,
  with -1 for an infinite sequence) do.
* The next term is chosen by the rule stated in the entry: the smallest digit `y ∈ {0, …, 9}`
  such that `a + 10 * (a % 10) + y` has leading digit `y`. (`y = 0` can never work, since a
  positive number has a nonzero leading digit; it is kept to follow the entry literally.)
  "Finite" means that at some step no such digit exists, i.e. the iteration reaches `none`.
* Base 10 throughout, as in the entry. The other-base analogues (arXiv:2408.03434) are not
  formalized here.
-/

namespace OMA.S_oeis_a121805

/-- The leading (most significant) decimal digit of `m`; it is `0` only for `m = 0`. -/
def leadingDigit (m : ℕ) : ℕ := (Nat.digits 10 m).getLastD 0

/-- One step of the comma rule: from a term `a` with last digit `x = a % 10`, the next term is
`a + 10 * x + y` for the smallest digit `y` that is the leading digit of that number, and
`none` (the sequence stops) if there is no such digit. -/
def commaNext (a : ℕ) : Option ℕ :=
  ((List.range 10).find? fun y => leadingDigit (a + 10 * (a % 10) + y) = y).map
    fun y => a + 10 * (a % 10) + y

/-- The comma sequence started at `s`: `commaSeq s n` is its `(n+1)`-st term, or `none` once
the sequence has stopped. `commaSeq 1` is A121805. -/
def commaSeq (s : ℕ) : ℕ → Option ℕ
  | 0 => some s
  | n + 1 => (commaSeq s n).bind commaNext

/-- **Sloane's conjecture on A121805.** For every positive initial term, the comma sequence is
finite: at some step no admissible next term exists. -/
theorem main : ∀ s : ℕ, 0 < s → ∃ n : ℕ, commaSeq s n = none := by
  sorry

end OMA.S_oeis_a121805

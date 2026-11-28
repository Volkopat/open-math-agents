import Mathlib

/-!
# A356990: a(n) = n - a^[4](n - a^[5](n-1)) with a(1) = 1, where a^[4] and a^[5] denote the
4-fold and 5-fold iterates of a.

Source: https://oeis.org/A356990 (Peter Bala). Related: https://oeis.org/A003269, https://oeis.org/A014101
Credit: @Squee451

Data (offset 1): 1, 1, 2, 3, 4, 5, 5, 6, 7, 7, 8, 9, 10, 10, 11, 12, 13, 14, 14, 15, 16, 17, 18, 19, 19, 19, 20, ...

The entry's comments: the line graph of the sequence consists of a series of plateaus (where the
value a(n) remains constant as n increases) joined by lines of slope 1.
"The sequence of plateau heights begins 5, 7, 10, 14, 19, 26, 36, 50, ..., which appears to be A003269."
"The plateaus start at abscissa values n = 6, 9, 13, 18, 24, 33, 46, 64, ..., which appears to be A014101,
and terminate at abscissa values 7, 10, 14, 19, 26, 36, 50, ..., conjecturally A003269."

So, apart from the initial plateau a(1) = a(2) = 1 (which the entry's lists do not include), the
conjecture is that the plateaus are, in order, exactly the following: for i = 0, 1, 2, ..., a plateau
of height A003269(8+i) that starts at n = A014101(6+i) and ends at n = A003269(9+i).

Conventions.
* A plateau is a maximal run of at least two consecutive indices with the same value:
  `Plateau a s e h` says `1 ≤ s < e`, `a n = h` for `s ≤ n ≤ e`, the term before the run (if any)
  differs from `h`, and the term after the run differs from `h`.
* The sequence has offset 1. `nestedPrefix n` is the list `[a(0), a(1), ..., a(n)]` with the
  placeholder `a(0) = 0`, built term by term from the recurrence; `f` looks a value up in the list
  already built (default 0), and `f^[r]` is its r-fold iterate. For `n + 1 ≥ 2` the recurrence only
  ever looks up indices between 1 and n, and its subtractions do not truncate.
* `A003269` and `A014101` are defined by the recurrences in their OEIS titles, with the OEIS offsets
  (A003269: offset 0, a(0) = 0, a(1) = a(2) = a(3) = 1, a(n) = a(n-1) + a(n-4) and A014101: offset 0, starting 1, 1, 1, 3, a(n) = a(n-1) + a(n-4)).
-/

namespace OMA.S_oeis_a356990

/-- `[a(0), a(1), ..., a(n)]` for the nested recurrence, with the placeholder `a(0) = 0`. -/
def nestedPrefix : ℕ → List ℕ
  | 0 => [0]
  | n + 1 =>
    let xs := nestedPrefix n
    let f : ℕ → ℕ := fun k => xs.getD k 0
    xs ++ [if n = 0 then 1 else n + 1 - f^[4] (n + 1 - f^[5] n)]

/-- A356990 (1-indexed). -/
def a (n : ℕ) : ℕ := (nestedPrefix n).getD n 0

/-- A003269 (offset 0). -/
def A003269 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | n + 4 => A003269 (n + 3) + A003269 n

/-- A014101 (offset 0). -/
def A014101 : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | n + 4 => A014101 (n + 3) + A014101 n

/-- `[s, e]` is a maximal run of at least two consecutive indices on which `a` has the value `h`. -/
def Plateau (s e h : ℕ) : Prop :=
  1 ≤ s ∧ s < e ∧ (∀ n, s ≤ n → n ≤ e → a n = h) ∧ (s = 1 ∨ a (s - 1) ≠ h) ∧ a (e + 1) ≠ h

/-- The plateaus of height greater than 1 are exactly the conjectured ones. -/
theorem main : ∀ s e h : ℕ, 1 < h →
    (Plateau s e h ↔ ∃ i : ℕ, h = A003269 (8 + i) ∧ s = A014101 (6 + i) ∧ e = A003269 (9 + i)) := by
  sorry

end OMA.S_oeis_a356990

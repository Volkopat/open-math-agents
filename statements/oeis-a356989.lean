import Mathlib

/-!
# A356989: a(n) = n - a^[3](n - a^[4](n-1)) with a(1) = 1, where a^[3] and a^[4] denote the
3-fold and 4-fold iterates of a.

Source: https://oeis.org/A356989 (Peter Bala). Related: https://oeis.org/A000930, https://oeis.org/A179070
Credit: @Squee451

Data (offset 1): 1, 1, 2, 3, 4, 4, 5, 6, 6, 7, 8, 9, 9, 10, 11, 12, 13, 13, 13, 14, 15, 16, 17, 18, 19, 19, 19, ...

The entry's comments: the line graph of the sequence consists of a series of plateaus (where the
value a(n) remains constant as n increases) joined by lines of slope 1.
"The sequence of plateau heights begins 4, 6, 9, 13, 19, 28, 41, 60, ..., conjecturally A000930."
"The plateaus start at abscissa values n = 5, 8, 12, 17, 25, 37, 54, 79, ..., conjecturally A179070,
and terminate at abscissa values n = 6, 9, 13, 19, 28, 41, 60, ..., conjecturally A000930."

So, apart from the initial plateau a(1) = a(2) = 1 (which the entry's lists do not include), the
conjecture is that the plateaus are, in order, exactly the following: for i = 0, 1, 2, ..., a plateau
of height A000930(5+i) that starts at n = A179070(6+i) and ends at n = A000930(6+i).

Conventions.
* A plateau is a maximal run of at least two consecutive indices with the same value:
  `Plateau a s e h` says `1 ≤ s < e`, `a n = h` for `s ≤ n ≤ e`, the term before the run (if any)
  differs from `h`, and the term after the run differs from `h`.
* The sequence has offset 1. `nestedPrefix n` is the list `[a(0), a(1), ..., a(n)]` with the
  placeholder `a(0) = 0`, built term by term from the recurrence; `f` looks a value up in the list
  already built (default 0), and `f^[r]` is its r-fold iterate. For `n + 1 ≥ 2` the recurrence only
  ever looks up indices between 1 and n, and its subtractions do not truncate.
* `A000930` and `A179070` are defined by the recurrences in their OEIS titles, with the OEIS offsets
  (A000930: offset 0, a(0) = a(1) = a(2) = 1, a(n) = a(n-1) + a(n-3) and A179070: offset 1, a(1) = a(2) = a(3) = 1, a(4) = 3, a(n) = a(n-1) + a(n-3)).
-/

namespace OMA.S_oeis_a356989

/-- `[a(0), a(1), ..., a(n)]` for the nested recurrence, with the placeholder `a(0) = 0`. -/
def nestedPrefix : ℕ → List ℕ
  | 0 => [0]
  | n + 1 =>
    let xs := nestedPrefix n
    let f : ℕ → ℕ := fun k => xs.getD k 0
    xs ++ [if n = 0 then 1 else n + 1 - f^[3] (n + 1 - f^[4] n)]

/-- A356989 (1-indexed). -/
def a (n : ℕ) : ℕ := (nestedPrefix n).getD n 0

/-- A000930 (Narayana's cows sequence, offset 0). -/
def A000930 : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => A000930 (n + 2) + A000930 n

/-- A179070 (offset 1; the value at 0 is a placeholder). -/
def A179070 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 3
  | n + 5 => A179070 (n + 4) + A179070 (n + 2)

/-- `[s, e]` is a maximal run of at least two consecutive indices on which `a` has the value `h`. -/
def Plateau (s e h : ℕ) : Prop :=
  1 ≤ s ∧ s < e ∧ (∀ n, s ≤ n → n ≤ e → a n = h) ∧ (s = 1 ∨ a (s - 1) ≠ h) ∧ a (e + 1) ≠ h

/-- The plateaus of height greater than 1 are exactly the conjectured ones. -/
theorem main : ∀ s e h : ℕ, 1 < h →
    (Plateau s e h ↔ ∃ i : ℕ, h = A000930 (5 + i) ∧ s = A179070 (6 + i) ∧ e = A000930 (6 + i)) := by
  sorry

end OMA.S_oeis_a356989

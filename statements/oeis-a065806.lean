import Mathlib

/-!
# A065806: conjectures on a pseudo-random sequence

Source: https://oeis.org/A065806
Credit: @jagraj28

A065806 is defined by the program in the entry. Start with the array `b(x) = x` for every integer
`x`. For `i = 0, 1, 2, ...`: let `j = b(i) - b(i-1)`, set `a(i+1) = j + 1`, then swap the values
`b(i)` and `b(j)`. The sequence begins 2, 0, 4, 0, 5, 2, 8, 0, 7, 3, ...

The entry records four conjectures:
1. `-1 < a(n) < n + 2`;
2. if `a(n) = n + 1` then `a(n+1) = 0`;
3. all integers `> 1` occur in the sequence;
4. for each `c` in `[0, 1]` there is a subsequence `a(i_j)` with `(a(i_j) + 1)/(i_j + 3) → c`
   as `j → ∞`.

`main` is the conjunction of the four, for `n ≥ 1` (the sequence has offset 1).

Conventions:
* `state i : ℤ → ℤ` is the array `b` before step `i`; the swap is composition with
  `Equiv.swap i j`. A simulation of this definition reproduces the listed terms.
* A subsequence is given by a strictly increasing sequence of indices `i_j ≥ 1`.
-/

namespace OMA.S_oeis_a065806

open Filter Topology

/-- `state i` is the array `b` before step `i` of the program. -/
def state : ℕ → ℤ → ℤ
  | 0 => id
  | i + 1 =>
    let b := state i
    b ∘ Equiv.swap (i : ℤ) (b i - b ((i : ℤ) - 1))

/-- `a n` for `n ≥ 1`: the term written at step `n - 1`, namely `b(i) - b(i-1) + 1` with
`i = n - 1`. -/
def a (n : ℕ) : ℤ :=
  state (n - 1) ((n - 1 : ℕ) : ℤ) - state (n - 1) (((n - 1 : ℕ) : ℤ) - 1) + 1

/-- The four conjectures of OEIS A065806. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → -1 < a n ∧ a n < n + 2) ∧
    (∀ n : ℕ, 1 ≤ n → a n = n + 1 → a (n + 1) = 0) ∧
    (∀ m : ℤ, 1 < m → ∃ n : ℕ, 1 ≤ n ∧ a n = m) ∧
    (∀ c : ℝ, c ∈ Set.Icc 0 1 → ∃ i : ℕ → ℕ, StrictMono i ∧ (∀ j, 1 ≤ i j) ∧
      Tendsto (fun j => ((a (i j) : ℝ) + 1) / ((i j : ℝ) + 3)) atTop (𝓝 c)) := by
  sorry

end OMA.S_oeis_a065806

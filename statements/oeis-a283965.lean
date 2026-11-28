import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.List.Count

/-!
# OEIS A283965

Source: https://oeis.org/A283965
Credit: @AShahver

The sequence gives the one-based positions of 1 in the fixed point of
0 ↦ 1 and 1 ↦ 1010, starting at 1. Each image starts with 1, and every
iterate is a prefix of the next. The n-th 1 is present after n iterations.
-/

namespace OMA.S_oeis_a283965

abbrev Word := List Bool

def letter : Bool → Word
  | false => [true]
  | true => [true, false, true, false]

def subst (w : Word) : Word := w.flatMap letter

def iter : ℕ → Word
  | 0 => [true]
  | k + 1 => subst (iter k)

def ones (w : Word) : ℕ := w.count true

def nthOne : ℕ → Word → ℕ
  | 0, _ => 0
  | _, [] => 0
  | n + 1, false :: w => nthOne (n + 1) w + 1
  | 1, true :: _ => 1
  | n + 2, true :: w => nthOne (n + 1) w + 1

def a (n : ℕ) : ℕ := nthOne n (iter n)

theorem main : ∀ n : ℕ, 0 < n →
    -1 < Real.sqrt 3 * (n : ℝ) - (a n : ℝ) ∧
      Real.sqrt 3 * (n : ℝ) - (a n : ℝ) < 2 := by
  sorry

end OMA.S_oeis_a283965

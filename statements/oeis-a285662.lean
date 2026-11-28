import Mathlib

/-!
# A285662: positions of 0 in A285661 (Kimberling's limit conjecture)

Source: https://oeis.org/A285662 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A285662 (offset 1): positions of 0 in A285661; complement of A285663; data 3, 4, 7, 8, 15, 16, 19, ...
A285661 (offset 1) is the fixed point of the morphism 0 -> 11, 1 -> 1100; as a word
A285661 = 110011001...

The entry records:

  Conjecture:  a(n)/n -> (3 + sqrt(5))/2.

Reading of the source:
* The morphism `σ` sends the letter 0 to `11` and the letter 1 to `1100`. Since `σ(1)` begins
  with 1 and every image has length at least 2, `σ^k(1)` is a prefix of `σ^(k+1)(1)` and has
  length at least `2^k`, so these words converge to the infinite fixed point of `σ` beginning
  with 1. Iterating from 0 gives the same word (`σ(0) = 11`), which is how the entry shows it.
  `w i`, the letter at 0-based position `i`, is read off `σ^(i+1)(1)`, which is long enough.
* Positions are 1-based, as in the entry: `a n` (for `n ≥ 1`) is `1 +` the 0-based position of
  the `n`-th 0 of the word (`Nat.nth` counts from 0). The word has infinitely many 0s.
* `a(n)/n -> (3 + sqrt(5))/2` is a limit in `ℝ` as `n → ∞`.
-/

namespace OMA.S_oeis_a285662

open Filter Topology

/-- The morphism 0 -> 11, 1 -> 1100 on the letters 0 and 1 (any other letter is read as 1). -/
def σ : ℕ → List ℕ
  | 0 => [1, 1]
  | _ => [1, 1, 0, 0]

/-- `σ^k(1)`. -/
def iter (k : ℕ) : List ℕ := (fun u : List ℕ => u.flatMap σ)^[k] [1]

/-- A285661: the letter at 0-based position `i` of the fixed point of `σ` beginning with 1. -/
def w (i : ℕ) : ℕ := (iter (i + 1)).getD i 0

/-- A285662(n): the 1-based position of the `n`-th 0 in A285661 (`n ≥ 1`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => w i = 0) (n - 1) + 1

/-- Kimberling's conjecture: `a(n)/n → (3 + sqrt(5))/2`. -/
theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 ((3 + Real.sqrt 5) / 2)) := by
  sorry

end OMA.S_oeis_a285662

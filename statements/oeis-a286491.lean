import Mathlib

/-!
# OEIS A286491: gaps in {1,2,3} and a(n)/n -> 9/5

Source: https://oeis.org/A286491 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, May 11 2017), offset 1: Positions of 0 in A286490. Comment: a(n) - a(n-1) is in {1,2,3} for n>=2.
Conjecture: a(n)/n -> 9/5. Data: 1, 4, 6, 7, 10, 11, 13, 15, ...
A286490 (Clark Kimberling, May 11 2017): {0101->0}-transform of the Thue-Morse word A010060.
Its program: w1 = StringReplace[w, {0101 -> 0}] with w the Thue-Morse word.
A010060 (offset 0): the Thue-Morse sequence 0, 1, 1, 0, 1, 0, 0, 1, ..., a(n) = A000120(n) mod 2.

Formalization notes:
* t(n) is the parity of the number of 1s in the binary expansion of n (A010060, offset 0).
* The transform is StringReplace with the single rule 0101 -> 0 applied to the infinite word t:
  read from the left, at each position a 0101 starting there is replaced by 0 and skipped, any
  other letter is copied. `pos k` is the position of t read for the output letter k.
* `w` is the transform indexed from 0, and `a n` adds 1 to the 0-based index of the n-th 0 of
  `w`, so positions count from 1 as in the entry; `Nat.nth` counts its argument from 0.
* `main` is the conjunction of both statements of the excerpt: a(n) - a(n-1) is one of 1, 2 or 3
  for every n >= 2, and a(n)/n tends to 9/5 as a limit of real numbers.
-/

namespace OMA.S_oeis_a286491

open Filter Topology

/-- The Thue-Morse word A010060 (offset 0): t(n) is the parity of the number of 1s in the binary
expansion of n. -/
def tm (n : ℕ) : ℕ := (Nat.digits 2 n).count 1 % 2

/-- The scan of StringReplace with the rule 0101 -> 0 on the infinite word t, read from the left:
`pos k` is the position of t at which the output letter k (from 0) is produced; if 0101 starts
there it is replaced by 0 and skipped, otherwise the letter is copied. -/
def pos : ℕ → ℕ
  | 0 => 0
  | k + 1 => if tm (pos k) = 0 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 0 ∧ tm (pos k + 3) = 1
      then pos k + 4 else pos k + 1

/-- A286490 (0-indexed): the k-th letter of the {0101 -> 0}-transform of the Thue-Morse word. -/
def w (k : ℕ) : ℕ :=
  if tm (pos k) = 0 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 0 ∧ tm (pos k + 3) = 1 then 0
  else tm (pos k)

/-- A286491(n): the position, counted from 1 as in the entry, of the n-th 0 of A286490. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun k => w k = 0) (n - 1) + 1

/-- Kimberling: a(n) - a(n-1) is in {1,2,3} for n >= 2, and a(n)/n -> 9/5. -/
theorem main : (∀ n : ℕ, 2 ≤ n → a n - a (n - 1) = 1 ∨ a n - a (n - 1) = 2 ∨ a n - a (n - 1) = 3) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (9 / 5)) := by
  sorry

end OMA.S_oeis_a286491

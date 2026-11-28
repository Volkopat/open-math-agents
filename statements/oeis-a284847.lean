import Mathlib

/-!
# OEIS A284847: gaps in {1,2,3,4} and a(n)/n -> 9/4

Source: https://oeis.org/A284847 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, May 10 2017), offset 1: Positions of 1 in the {1100->0}-transform of A010060. Comment: a(n) - a(n-1) is in {1,2,3,4} for n>=2.
Conjecture: a(n)/n -> 9/4. Data: 2, 3, 5, 9, 11, 12, 14, 17, ...
The entry's program builds the transform with StringReplace[w, {1100 -> 0}] from the
Thue-Morse word w.
A010060 (offset 0): the Thue-Morse sequence 0, 1, 1, 0, 1, 0, 0, 1, ..., a(n) = A000120(n) mod 2.

Formalization notes:
* t(n) is the parity of the number of 1s in the binary expansion of n (A010060, offset 0).
* The transform is StringReplace with the single rule 1100 -> 0 applied to the infinite word t:
  read from the left, at each position a 1100 starting there is replaced by 0 and skipped, any
  other letter is copied. `pos k` is the position of t read for the output letter k.
* `w` is the transform indexed from 0, and `a n` adds 1 to the 0-based index of the n-th 1 of
  `w`, so positions count from 1 as in the entry; `Nat.nth` counts its argument from 0.
* `main` is the conjunction of both statements of the excerpt: a(n) - a(n-1) is one of 1, 2, 3 or 4
  for every n >= 2, and a(n)/n tends to 9/4 as a limit of real numbers.
-/

namespace OMA.S_oeis_a284847

open Filter Topology

/-- The Thue-Morse word A010060 (offset 0): t(n) is the parity of the number of 1s in the binary
expansion of n. -/
def tm (n : ℕ) : ℕ := (Nat.digits 2 n).count 1 % 2

/-- The scan of StringReplace with the rule 1100 -> 0 on the infinite word t, read from the left:
`pos k` is the position of t at which the output letter k (from 0) is produced; if 1100 starts
there it is replaced by 0 and skipped, otherwise the letter is copied. -/
def pos : ℕ → ℕ
  | 0 => 0
  | k + 1 => if tm (pos k) = 1 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 0 ∧ tm (pos k + 3) = 0
      then pos k + 4 else pos k + 1

/-- The k-th letter (from 0) of the {1100 -> 0}-transform of the Thue-Morse word. -/
def w (k : ℕ) : ℕ :=
  if tm (pos k) = 1 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 0 ∧ tm (pos k + 3) = 0 then 0
  else tm (pos k)

/-- A284847(n): the position, counted from 1 as in the entry, of the n-th 1 of the transform. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun k => w k = 1) (n - 1) + 1

/-- Kimberling: a(n) - a(n-1) is in {1,2,3,4} for n >= 2, and a(n)/n -> 9/4. -/
theorem main : (∀ n : ℕ, 2 ≤ n → a n - a (n - 1) = 1 ∨ a n - a (n - 1) = 2 ∨ a n - a (n - 1) = 3 ∨ a n - a (n - 1) = 4) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (9 / 4)) := by
  sorry

end OMA.S_oeis_a284847

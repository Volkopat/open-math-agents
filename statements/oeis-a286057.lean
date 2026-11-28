import Mathlib

/-!
# OEIS A286057: a(n)/n -> 4/3

Source: https://oeis.org/A286057 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, May 08 2017), offset 1: Positions of 1 in A286055; complement of A286056.
Conjecture: a(n)/n -> 4/3. Data: 2, 3, 4, 6, 7, 9, 10, 11, ...
A286055 (Clark Kimberling, May 08 2017): {010->1}-transform of the Thue-Morse word A010060.
Its example: A010060 = 0110100110010110100101100..., and the transform begins 0111011011111110011101101110...
A010060 (offset 0): the Thue-Morse sequence 0, 1, 1, 0, 1, 0, 0, 1, ..., a(n) = A000120(n) mod 2.

Formalization notes:
* t(n) is the parity of the number of 1s in the binary expansion of n (A010060, offset 0).
* The transform is StringReplace with the single rule 010 -> 1 applied to the infinite word t:
  read from the left, at each position a 010 starting there is replaced by 1 and skipped, any
  other letter is copied. `pos k` is the position of t read for the output letter k.
* The rule 010 -> 1 is the one in the name of A286055, and it reproduces the data of A286055 and
  A286057 and the transform shown in the example. The Mathematica programs of both entries pass
  the rule 010 -> 0 to StringReplace, which gives other terms (2, 3, 6, 7, 10, ...) and the limit
  2 instead of 4/3.
* `w` is the transform indexed from 0, and `a n` adds 1 to the 0-based index of the n-th 1 of
  `w`, so positions count from 1 as in the entry; `Nat.nth` counts its argument from 0.
* `main` states the conjecture of the excerpt: a(n)/n tends to 4/3 as a limit of real numbers.
-/

namespace OMA.S_oeis_a286057

open Filter Topology

/-- The Thue-Morse word A010060 (offset 0): t(n) is the parity of the number of 1s in the binary
expansion of n. -/
def tm (n : ℕ) : ℕ := (Nat.digits 2 n).count 1 % 2

/-- The scan of StringReplace with the rule 010 -> 1 on the infinite word t, read from the left:
`pos k` is the position of t at which the output letter k (from 0) is produced; if 010 starts
there it is replaced by 1 and skipped, otherwise the letter is copied. -/
def pos : ℕ → ℕ
  | 0 => 0
  | k + 1 => if tm (pos k) = 0 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 0
      then pos k + 3 else pos k + 1

/-- A286055 (0-indexed): the k-th letter of the {010 -> 1}-transform of the Thue-Morse word. -/
def w (k : ℕ) : ℕ :=
  if tm (pos k) = 0 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 0 then 1
  else tm (pos k)

/-- A286057(n): the position, counted from 1 as in the entry, of the n-th 1 of A286055. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun k => w k = 1) (n - 1) + 1

/-- Kimberling's conjecture: a(n)/n -> 4/3. -/
theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (4 / 3)) := by
  sorry

end OMA.S_oeis_a286057

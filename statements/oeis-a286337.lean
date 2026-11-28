import Mathlib

/-!
# OEIS A286337: a(n)/n -> 3/2 for the positions of 0 in A286336

Source: https://oeis.org/A286337 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, May 2017), offset 1: Positions of 0 in A286336; complement of A286338.
Comment: Conjecture: a(n)/n -> 3/2. Data: 1, 2, 3, 4, 7, 8, 10, 11, ...
A286336 (Clark Kimberling, May 08 2017): {1101->0}-transform of the Thue-Morse word A010060.
Its program: w1 = StringReplace[w, {1101 -> 0}] with w the Thue-Morse word.
A010060 (offset 0): the Thue-Morse sequence 0, 1, 1, 0, 1, 0, 0, 1, ..., a(n) = A000120(n) mod 2.

Formalization notes:
* t(n) is the parity of the number of 1s in the binary expansion of n (A010060, offset 0).
* The transform is StringReplace with the single rule 1101 -> 0 applied to the infinite word t:
  read from the left, at each position a 1101 starting there is replaced by 0 and skipped, any
  other letter is copied. `pos k` is the position of t read for the output letter k.
* `w` is A286336 indexed from 0, and `a n` adds 1 to the 0-based index of the n-th 0 of `w`, so
  positions count from 1 as in the entries; `Nat.nth` counts its argument from 0.
* `main` is the conjecture as a limit of real numbers: a(n)/n tends to 3/2.
-/

namespace OMA.S_oeis_a286337

open Filter Topology

/-- The Thue-Morse word A010060 (offset 0): t(n) is the parity of the number of 1s in the binary
expansion of n. -/
def tm (n : ℕ) : ℕ := (Nat.digits 2 n).count 1 % 2

/-- The scan of StringReplace with the rule 1101 -> 0 on the infinite word t, read from the left:
`pos k` is the position of t at which the output letter k (from 0) is produced; if 1101 starts
there it is replaced by 0 and skipped, otherwise the letter is copied. -/
def pos : ℕ → ℕ
  | 0 => 0
  | k + 1 => if tm (pos k) = 1 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 0 ∧ tm (pos k + 3) = 1
      then pos k + 4 else pos k + 1

/-- A286336 (0-indexed): the k-th letter of the {1101 -> 0}-transform of the Thue-Morse word. -/
def w (k : ℕ) : ℕ :=
  if tm (pos k) = 1 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 0 ∧ tm (pos k + 3) = 1 then 0
  else tm (pos k)

/-- A286337(n): the position, counted from 1 as in the entry, of the n-th 0 of A286336. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun k => w k = 0) (n - 1) + 1

/-- Kimberling's conjecture: a(n)/n -> 3/2. -/
theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (3 / 2)) := by
  sorry

end OMA.S_oeis_a286337

import Mathlib

/-!
# A071824: Number of integers <= n whose largest prime factor is of the form 4k + 1

Source: https://oeis.org/A071824
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
Let `a(n)` be the number of integers `1 ≤ m ≤ n` whose largest prime factor is congruent
to `1 (mod 4)`, and let `b(n)` be the number of integers `1 ≤ m ≤ n` whose largest prime
factor is congruent to `3 (mod 4)`.
Then for all `n > 1000`:
  `a(n) - n / 2 < -sqrt(n)` and `b(n) - n / 2 > sqrt(n)`.

Conventions:
- `gpf m` is `m.primeFactors.sup id` (which is `0` for `m ≤ 1`, and the largest prime factor for `m ≥ 2`).
-/

namespace OMA.S_oeis_a071824

def gpf (m : ℕ) : ℕ :=
  m.primeFactors.sup id

def aSeq (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter fun m => gpf m % 4 = 1).card

def bSeq (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter fun m => gpf m % 4 = 3).card

theorem main :
    ∀ n : ℕ, n > 1000 →
      (aSeq n : ℝ) - (n : ℝ) / 2 < -Real.sqrt (n : ℝ) ∧
      (bSeq n : ℝ) - (n : ℝ) / 2 > Real.sqrt (n : ℝ) := by
  sorry

end OMA.S_oeis_a071824

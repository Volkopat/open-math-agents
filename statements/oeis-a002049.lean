import Mathlib

/-!
# OEIS A002049 (prime numbers of measurement, partial sums): Andrews' asymptotic

Source: https://oeis.org/A002049
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A002049 is the sequence of partial sums of A002048, the segmented numbers (prime numbers of
measurement): `1, 2, 4, 5, 8, 10, 14, …`, each term being the least integer larger than the
previous one that is not a sum of two or more consecutive earlier terms. Conjecture (Andrews,
recorded in the entry): `a(n) ~ (1/2) n² log n / log log n`.

Encoding: `s 0, s 1, …` is A002048 (characterised by its defining recursion, which determines
it uniquely), and `a(n) = s 0 + ⋯ + s (n-1)`.
-/

namespace OMA.S_oeis_a002049

open Filter

/-- `s i + ⋯ + s j`. -/
def blockSum (s : ℕ → ℕ) (i j : ℕ) : ℕ := ∑ k ∈ Finset.Icc i j, s k

/-- `s` is the segmented sequence A002048. -/
def IsSegmented (s : ℕ → ℕ) : Prop :=
  s 0 = 1 ∧ ∀ n, s (n + 1) =
    sInf {m : ℕ | s n < m ∧ ∀ i j, i < j → j ≤ n → blockSum s i j ≠ m}

/-- Andrews' conjecture. -/
theorem main :
    ∀ s : ℕ → ℕ, IsSegmented s →
      Tendsto (fun n : ℕ => ((∑ k ∈ Finset.range n, s k : ℕ) : ℝ) /
        ((1 / 2) * (n : ℝ) ^ 2 * Real.log n / Real.log (Real.log n))) atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a002049

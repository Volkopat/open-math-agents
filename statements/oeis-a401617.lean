import Mathlib

/-!
# A401617: Maximum run of equal digits across all bases

Source: https://oeis.org/A401617
Credit: @gblacher2
-/

namespace OMA.S_oeis_a401617

/-- Some base at least two has a block of `k` equal digits in the expansion of `n`.
Reversing the digit order preserves the existence of such a block. -/
def HasRun (n k : ℕ) : Prop :=
  ∃ b d : ℕ, 2 ≤ b ∧ (List.replicate k d).IsInfix (Nat.digits b n)

/-- For every `k ≥ 2`, infinitely many numbers have maximum run length `k`.
A longer run would contain a run of length `k + 1`. -/
theorem main :
    ∀ k : ℕ, 2 ≤ k → {n : ℕ | HasRun n k ∧ ¬ HasRun n (k + 1)}.Infinite := by
  sorry

end OMA.S_oeis_a401617

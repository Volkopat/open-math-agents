import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Defs

/-!
# A190302: a multiple beginning with the digit one

Source: https://oeis.org/A190302 (OEIS Foundation, CC BY-SA 4.0).
Credit: @maaaakks. Formalized with Codex (GPT-6.2 Sol).

For `n ≥ 1`, `a(n)` is the least positive `h` such that the decimal expansion
of `h * n` starts with 1. Felix Fröhlich conjectures `a(n) < 6` for every
positive `n`. Charles R. Greathouse IV stated the same bound for the least
multiple in the comments to https://oeis.org/A187285 on March 7, 2011.
A natural number starts with 1 in decimal exactly when it is in one of the
intervals `[10^k, 2 * 10^k)`, with `k ≥ 0`.
-/

namespace OMA.S_oeis_a190302

/-- The decimal expansion of `m` has leading digit one. -/
def BeginsWithOne (m : ℕ) : Prop := ∃ k : ℕ, 10 ^ k ≤ m ∧ m < 2 * 10 ^ k

/-- The least positive multiplier which produces leading digit one exists and is below six. -/
theorem main : ∀ n : ℕ, 0 < n →
    ∃ h : ℕ, IsLeast {m : ℕ | 0 < m ∧ BeginsWithOne (m * n)} h ∧ h < 6 := by
  sorry

end OMA.S_oeis_a190302

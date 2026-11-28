import Mathlib

/-!
# OEIS A193262

Vladimir Shevelev conjectures that all sufficiently late terms are positive.
A representation is counted once by its smaller prime summand. The two summands may coincide.

Source: https://oeis.org/A193262
Credit: @AlfredMelson
-/

namespace OMA.S_oeis_a193262

/-- Number of qualifying unordered representations of twice the prime r. -/
def representations (r : ℕ) : ℕ :=
  ((Finset.Icc 2 r).filter fun p =>
    let q := 2 * r - p
    p.Prime ∧ q.Prime ∧ (p * q - 2).Prime).card

/-- The OEIS index starts at one, with the first prime equal to two. -/
theorem main :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n → 0 < representations (Nat.nth Nat.Prime (n - 1)) := by
  sorry

end OMA.S_oeis_a193262

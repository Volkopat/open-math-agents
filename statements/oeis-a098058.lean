import Mathlib

/-!
# Arbitrarily long strings in OEIS A098058

The sequence keeps a prime when its gap to the next prime is not divisible
by four. Jonathan Sondow conjectured that it contains arbitrarily long
strings of consecutive primes.

Source: https://oeis.org/A098058 (OEIS Foundation, CC BY-SA 4.0).
Credit: @wtho704
-/

namespace OMA.S_oeis_a098058

/-- The gap following position `i` in Mathlib's zero-based prime sequence. -/
noncomputable def primeGapAt (i : ℕ) : ℕ :=
  Nat.nth Nat.Prime (i + 1) - Nat.nth Nat.Prime i

theorem main : ∀ length : ℕ, 0 < length →
    ∃ start : ℕ, ∀ i < length, ¬ 4 ∣ primeGapAt (start + i) := by
  sorry

end OMA.S_oeis_a098058

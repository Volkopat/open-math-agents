import Mathlib

/-!
# Does the sequence aᵢ hit every positive integer infinitely many times for all i ≥ 1?

Source: https://mathoverflow.net/questions/396438
Credit: @datdzrgb
-/

namespace OMA.S_mo_396438

/-- The source starts at index 1; the value at index 0 is unused. -/
def a (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      let prev := a i (n + 1)
      if i + 1 ∣ prev then prev / (i + 1) else n + 2 - prev

theorem main :
    ∀ i : ℕ, 1 ≤ i → ∀ m : ℕ, 0 < m → {n : ℕ | 0 < n ∧ a i n = m}.Infinite := by
  sorry

end OMA.S_mo_396438

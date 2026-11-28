import Mathlib.Data.Nat.Prime.Defs

/-!
# A proposed primality test for numbers of the form 2² + n²

Source: https://mathoverflow.net/questions/239499
Credit: @bmander
-/

namespace OMA.S_mo_239499

theorem main : ∀ n : ℕ, n % 2 = 1 →
    let N := 2 ^ 2 + n ^ 2
    Nat.Prime N ↔ N ∣ 2 ^ ((N - 1) / 2) + 1 := by
  sorry

end OMA.S_mo_239499

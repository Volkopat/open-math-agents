import Mathlib.Data.Nat.Basic

namespace OMA.S_oeis_a271623

/-- The orbit starting at 7, with odd terms sent to 7n + 1 and even terms halved. -/
def term : ℕ → ℕ
  | 0 => 7
  | n + 1 =>
    let previous := term n
    if previous % 2 = 1 then 7 * previous + 1 else previous / 2

/-- No term equals an earlier term. Source: https://oeis.org/A271623 -/
theorem main : ∀ j k : ℕ, j < k → term k ≠ term j := by
  sorry

end OMA.S_oeis_a271623

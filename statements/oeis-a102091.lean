import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Int.Basic

/-!
Source: https://oeis.org/A102091, conjecture of Steven Lu.
OEIS Foundation, CC BY-SA 4.0.
-/

namespace OMA.S_oeis_a102091

/-- A102091 is defined by the recurrence in the source entry for the matching counts.
At k this triple holds the terms with OEIS indices k+1, k+2, and k+3. -/
def consecutiveCounts : ℕ → ℤ × ℤ × ℤ
  | 0 => (12, 32, 108)
  | k + 1 =>
    let (a, b, c) := consecutiveCounts k
    (b, c, 5 * c - 5 * b + a)

/-- A centered n-gonal number, with k rings surrounding the center. -/
def centered (n : ℤ) (k : ℕ) : ℤ := 1 + n * (↑(k * (k + 1) / 2) : ℤ)

theorem main : ∀ n : ℤ, 6 < n →
    ((∀ (k p : ℕ), p.Prime → (p % 12 = 5 ∨ p % 12 = 7) → ¬ ((p : ℤ) ∣ centered n k)) ↔
      ∃ k : ℕ, (consecutiveCounts k).1 = n) := by
  sorry

end OMA.S_oeis_a102091

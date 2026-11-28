import Mathlib

/-!
# The least number of squares representing minus one modulo a positive integer

Source: https://oeis.org/A227781 (OEIS Foundation, CC BY-SA 4.0).
The empty list represents zero, as required for the first term at modulus one.
-/

namespace OMA.S_oeis_a227781

/-- Exactly k integer squares have sum congruent to minus one modulo n. -/
def Represents (n k : ℕ) : Prop :=
  ∃ xs : List ℤ, xs.length = k ∧ (n : ℤ) ∣ (xs.map (fun x => x ^ 2)).sum + 1

theorem main : ∀ n : ℕ, 0 < n →
    (IsLeast {k : ℕ | Represents n k} 4 ↔ 8 ∣ n) ∧
    (IsLeast {k : ℕ | Represents n k} 3 ↔ n % 8 = 4) := by
  sorry

end OMA.S_oeis_a227781

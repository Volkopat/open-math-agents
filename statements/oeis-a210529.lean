import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Bounds.Defs

/-!
# Existence of the least congruence prime (OEIS A210529)

Source: https://oeis.org/A210529 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

The sequence takes the least candidate, either 1 or a prime different from
the input prime, whose square is congruent to the input prime's square
modulo every prime below its square root. The exclusion of the input prime
is explicit in the PARI program in the source. The conjecture concerns
existence at every positive index.
-/

namespace OMA.S_oeis_a210529

noncomputable def primeAt (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

def Candidates (p : ℕ) : Set ℕ :=
  {q | (q = 1 ∨ q.Prime) ∧ q ≠ p ∧
    ∀ r : ℕ, r.Prime → r ^ 2 < p → q ^ 2 ≡ p ^ 2 [MOD r]}

theorem main : ∀ n : ℕ, 0 < n → ∃ q : ℕ, IsLeast (Candidates (primeAt n)) q := by
  sorry

end OMA.S_oeis_a210529

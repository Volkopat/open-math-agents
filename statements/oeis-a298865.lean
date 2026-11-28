import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Group.Even

/-!
# Unique differences of squares in OEIS A298865

Clark Kimberling's conjecture characterizes the members of A298865 after its first
term, 2. The sequence consists of the primes and four times the primes.
Source: https://oeis.org/A298865 (OEIS Foundation, CC BY-SA 4.0).
Lean statement: @cjchaffin.
-/

namespace OMA.S_oeis_a298865

theorem main : ∀ n : ℕ,
    (n ≠ 2 ∧ (Nat.Prime n ∨ ∃ p : ℕ, Nat.Prime p ∧ n = 4 * p)) ↔
      ¬ IsSquare n ∧ ∃! xy : ℕ × ℕ, xy.2 < xy.1 ∧ xy.1 ^ 2 = n + xy.2 ^ 2 := by
  sorry

end OMA.S_oeis_a298865

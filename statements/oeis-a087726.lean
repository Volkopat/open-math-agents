import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Counting square-zero matrices over the integers modulo n

Robert Israel proposed an exact prime-power count, and Ben Branman asked when
the count is the square of the modulus. The fourfold products below express
Israel's quotient by four using integer arithmetic, including the parity sign.

Source: https://oeis.org/A087726
Credit: @DomTheDeveloper
-/

namespace OMA.S_oeis_a087726

/-- The number of two-by-two matrices whose square vanishes modulo n. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {M : Matrix (Fin 2) (Fin 2) (ZMod n) // M * M = 0}

/-- Branman's squarefree criterion and Israel's prime-power formula. -/
theorem main :
    (∀ n : ℕ, 0 < n → (a n = n ^ 2 ↔ Squarefree n)) ∧
    (∀ p k : ℕ, p.Prime → 0 < k →
      4 * (a (p ^ k) : ℤ) =
        (1 + 3 * (p : ℤ) ^ 2 + 2 * k * ((p : ℤ) ^ 2 - 1) +
          (-1 : ℤ) ^ k * ((p : ℤ) ^ 2 - 1)) * (p : ℤ) ^ (2 * k - 2)) := by
  sorry

end OMA.S_oeis_a087726

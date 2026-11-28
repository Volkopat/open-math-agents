import Mathlib

/-!
# OEIS A037225

Source: https://oeis.org/A037225 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Ciphore

`a(n) = φ(2n + 1)`. Alain Rocchelli's comments conjecture that, when `2n + 1`
is composite, `a(n)` does not divide `2n`, and that `a(n)` is never equal to `n`.
-/

namespace OMA.S_oeis_a037225

/-- Euler's totient of `2n + 1`. -/
def a (n : ℕ) : ℕ := (2 * n + 1).totient

theorem main :
    (∀ n : ℕ, (∃ d : ℕ, d ∣ 2 * n + 1 ∧ 1 < d ∧ d < 2 * n + 1) → ¬ a n ∣ 2 * n) ∧
    ∀ n : ℕ, a n ≠ n := by
  sorry

end OMA.S_oeis_a037225

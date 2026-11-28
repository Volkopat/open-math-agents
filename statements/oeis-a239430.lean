import Mathlib

/-!
# A prime count and a square count in two summand intervals

Source: https://oeis.org/A239430 (Zhi-Wei Sun)
Credit: @pyaf
-/

namespace OMA.S_oeis_a239430

/-- Number of primes in the interval (k, 2k]. -/
def intervalCount (k : ℕ) : ℕ := Nat.primeCounting (2 * k) - Nat.primeCounting k

/-- A239430, indexed from 1. The two summands have distinct roles. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter fun k =>
    (intervalCount k).Prime ∧ IsSquare (intervalCount (n - k))).card

theorem main :
    (∀ n : ℕ, 4 < n → 0 < a n) ∧
    (∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n ∈ ([5, 6, 20] : List ℕ))) := by
  sorry

end OMA.S_oeis_a239430

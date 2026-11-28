import Mathlib

/-!
# Prime counts in two summand intervals

Source: https://oeis.org/A239428 (Zhi-Wei Sun)
Credit: @pyaf
-/

namespace OMA.S_oeis_a239428

/-- Number of primes in the interval (k, 2k]. -/
def intervalCount (k : ℕ) : ℕ := Nat.primeCounting (2 * k) - Nat.primeCounting k

/-- A239428, indexed from 1. The smaller summand k determines its partner n-k. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (n / 2)).filter fun k =>
    (intervalCount k).Prime ∧ (intervalCount (n - k)).Prime).card

theorem main :
    (∀ n : ℕ, 9 < n → 0 < a n) ∧
    (∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n ∈ ([8, 10, 11, 26, 33, 50, 52] : List ℕ))) := by
  sorry

end OMA.S_oeis_a239428

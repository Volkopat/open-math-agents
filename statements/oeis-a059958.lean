import Mathlib

/-!
# Wilson's conjecture comparing the first occurrences of prime-factor counts

Source: https://oeis.org/A059958 and https://oeis.org/A069354
Credit: @pyaf
-/

namespace OMA.S_oeis_a059958

/-- A059958(n), for n ≥ 1. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ n ≤ (m * (m + 1)).primeFactors.card}

/-- A069354(n), the smallest base with exactly n prime factors across b and b-1. -/
noncomputable def base (n : ℕ) : ℕ :=
  sInf {b : ℕ | 2 ≤ b ∧ b.primeFactors.card + (b - 1).primeFactors.card = n}

theorem main : ∀ n : ℕ, 0 < n → a n = base n - 1 := by
  sorry

end OMA.S_oeis_a059958

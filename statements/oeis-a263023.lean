import Mathlib

/-!
# A263023: Largest integer k such that prime(n+1) < prime(n)^(1+1/k).

Source: https://oeis.org/A263023
Credit: @azmiozgen

Conjecture (Firoozbakht's conjecture, restated in the entry for this sequence): a(n) >= n.

Formalization notes:
* prime(n) = `Nat.nth Nat.Prime (n - 1)` (prime(1) = 2). Since prime(n)^(1+1/k) decreases in k,
  a(n) ≥ n is equivalent to prime(n+1) < prime(n)^(1+1/n), which is stated (real powers).
* Controls (computed): prime(n+1) < prime(n)^(1+1/n) for 1 ≤ n < 100000; the entry's terms begin
  1, 2, 4, 4, 14, 9, 25.
-/

namespace OMA.S_oeis_a263023

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `a(n) ≥ n` for every `n ≥ 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → (prime (n + 1) : ℝ) < (prime n : ℝ) ^ (1 + 1 / (n : ℝ)) := by
  sorry

end OMA.S_oeis_a263023

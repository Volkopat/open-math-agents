import Mathlib

/-!
# A064402: Numbers k such that prime(k) + k is prime, where prime(k) is the k-th prime.

Source: https://oeis.org/A064402
Credit: @azmiozgen

Conjecture (Zak Seidov, Nov 10 2013, from the entry): the first differences include all even
integers.

Formalization notes:
* prime(k) = `Nat.nth Nat.Prime (k - 1)` (prime(1) = 2); the terms are the k ≥ 1 with prime(k) + k
  prime, and a(n) (offset 1) is the n-th term in increasing order.
* Stated as: for every even d > 0 there is n ≥ 1 with a(n+1) - a(n) = d.
* Controls (computed): the terms begin 1, 2, 4, 6, 18, 22, 24, 26, 32, 34, 42, 48, as in the entry;
  among the terms below 6000 every even difference up to 42 occurs, as do 46, 48, 50.
-/

namespace OMA.S_oeis_a064402

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `k` is a term: `k ≥ 1` and `prime(k) + k` is prime. -/
def IsTerm (k : ℕ) : Prop := 1 ≤ k ∧ (prime k + k).Prime

/-- A064402(n), offset 1. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- Every positive even number is a first difference of the sequence. -/
theorem main : ∀ d : ℕ, 0 < d → Even d → ∃ n : ℕ, 1 ≤ n ∧ a (n + 1) - a n = d := by
  sorry

end OMA.S_oeis_a064402

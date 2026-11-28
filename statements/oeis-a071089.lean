import Mathlib

/-!
# A071089: Remainder when sum of first n primes is divided by n-th prime.

Source: https://oeis.org/A071089
Credit: @darealpandaboi

Conjecture: every nonnegative integer can appear in the sequence at most finitely many times.
(Another contributor conjectures the opposite; the statement below is the first conjecture.)

Translation notes.
* The n-th prime (n >= 1) is Nat.nth Nat.Prime (n - 1), and the sum of the first n primes is
  the sum of Nat.nth Nat.Prime i for i < n. a(n) is that sum mod the n-th prime.
* This reproduces all listed terms (checked by computer).
-/

namespace OMA.S_oeis_a071089

/-- The sum of the first n primes, mod the n-th prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  (∑ i ∈ Finset.range n, Nat.nth Nat.Prime i) % Nat.nth Nat.Prime (n - 1)

theorem main : ∀ t : ℕ, {n : ℕ | 1 ≤ n ∧ a n = t}.Finite := by
  sorry

end OMA.S_oeis_a071089

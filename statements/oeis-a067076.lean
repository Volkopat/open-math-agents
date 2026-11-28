import Mathlib

/-!
# A067076: Numbers k such that 2*k + 3 is a prime.

Source: https://oeis.org/A067076
Credit: @rickmanelius

Conjecture (R. J. Mathar): a(n) = A008507(n) + n - 1 = A005097(n) - 1 = A102781(n+1) - 1.

The sequences referred to (OEIS names and offsets):
* A008507 (offset 1): number of odd composite numbers less than the n-th odd prime.
* A005097 (offset 1): (odd primes - 1)/2, so A005097(n) = (prime(n+1) - 1)/2.
* A102781 (offset 1): number of positive even numbers less than the n-th prime.

Formalization notes:
* Offset 1, as in the entry. `a n` is the n-th natural number k (counting from n = 1, in
  increasing order) such that 2k + 3 is prime: `Nat.nth` of that predicate at index n - 1
  (`Nat.nth` counts from 0). The data begin 0, 1, 2, 4, 5, 7, 8, 10, 13, ...
* `prime n` is the n-th prime with prime 1 = 2, that is `Nat.nth Nat.Prime (n - 1)`. The n-th
  odd prime is then `prime (n + 1)`, so prime 2 = 3 is the first odd prime.
* An odd composite number is an odd m with 1 < m and m not prime.
* The claims are stated for every n ≥ 1, the indices of the sequence. They are stated in ℤ,
  so every subtraction is the true one (no truncation at 0).
-/

namespace OMA.S_oeis_a067076

/-- The n-th prime, with offset 1: prime 1 = 2, prime 2 = 3, prime 3 = 5, ... -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A067076, offset 1: the n-th number k (in increasing order) such that 2k + 3 is prime. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun k => (2 * k + 3).Prime) (n - 1)

/-- A008507, offset 1: the number of odd composite numbers less than the n-th odd prime. -/
noncomputable def A008507 (n : ℕ) : ℕ :=
  ((Finset.range (prime (n + 1))).filter (fun m => Odd m ∧ 1 < m ∧ ¬ m.Prime)).card

/-- A005097, offset 1: (odd primes - 1)/2, the n-th term being (prime(n+1) - 1)/2. -/
noncomputable def A005097 (n : ℕ) : ℕ := (prime (n + 1) - 1) / 2

/-- A102781, offset 1: the number of positive even numbers less than the n-th prime. -/
noncomputable def A102781 (n : ℕ) : ℕ :=
  ((Finset.range (prime n)).filter (fun m => 0 < m ∧ Even m)).card

/-- Mathar's conjecture: a(n) = A008507(n) + n - 1 = A005097(n) - 1 = A102781(n+1) - 1 for
every n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ((a n : ℤ) = (A008507 n : ℤ) + n - 1 ∧
      (a n : ℤ) = (A005097 n : ℤ) - 1 ∧
      (a n : ℤ) = (A102781 (n + 1) : ℤ) - 1) := by
  sorry

end OMA.S_oeis_a067076

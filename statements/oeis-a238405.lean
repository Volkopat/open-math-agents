import Mathlib

/-!
# A238405: a(n) = |{0 < k < n: prime(k) + pi(n-k) is a triangular number}|, where pi(.) is given by A000720.

Source: https://oeis.org/A238405
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) > 0 for all n > 6, and a(n) = 1 only for n = 5, 7,
13, 16, 18, 24, 29, 71, 72, 158.

Formalization notes:
* pi = `Nat.primeCounting` (pi(x) = number of primes ≤ x); prime(n) = `Nat.nth Nat.Prime (n - 1)`
  (prime(1) = 2).
* Triangular numbers are t(t+1)/2, t ≥ 0. "a(n) = 1 only for n in S" is stated as: a(n) = 1 iff
  n ∈ S.
* Controls (computed): a(1..25) = 0, 0, 2, 0, 1, 0, 1, 2, 3, 3, 2, 2, 1, 3, 3, 1, 2, 1, 2, 5, 3, 3, 4,
  1, 2, as in the entry; for n < 200, a(n) = 1 exactly at the listed n, and a(n) > 0 for 6 < n < 160.
-/

namespace OMA.S_oeis_a238405

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

open Classical in
/-- A238405(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter fun k =>
    ∃ t : ℕ, prime k + Nat.primeCounting (n - k) = t * (t + 1) / 2).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 6 < n → 0 < a n) ∧
      ∀ n : ℕ, a n = 1 ↔ n ∈ ({5, 7, 13, 16, 18, 24, 29, 71, 72, 158} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a238405

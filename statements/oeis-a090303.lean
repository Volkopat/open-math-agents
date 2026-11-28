import Mathlib

/-!
# A090303: Begin with n and consider numbers obtained by successively subtracting 2,3,5,7,11,...; a(n) = largest prime that arises, i.e., largest prime of the form n - sum prime(r), or 0 if no such prime exists.

Source: https://oeis.org/A090303
Credit: @darealpandaboi

Conjecture: there are finitely many zeros in this sequence.

Translation notes.
* The numbers that arise are n - (2 + 3 + ... + prime(r)) for r >= 1 (n itself is not one of
  them: a(5) = 3). a(n) = 0 exactly when none of them is prime. In ℕ, n - S with S > n is 0,
  which is not prime, so truncated subtraction adds no spurious primes.
* This reproduces all listed terms (checked by computer). Zeros keep occurring below 20000
  (the last ones found are 12293, 14652, 16866); the statement is the conjecture as given.
-/

namespace OMA.S_oeis_a090303

/-- The sum of the first r primes. -/
noncomputable def S (r : ℕ) : ℕ := ∑ i ∈ Finset.range r, Nat.nth Nat.Prime i

theorem main :
    {n : ℕ | 1 ≤ n ∧ ¬ ∃ r : ℕ, 1 ≤ r ∧ (n - S r).Prime}.Finite := by
  sorry

end OMA.S_oeis_a090303

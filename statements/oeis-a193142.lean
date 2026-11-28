import Mathlib

/-!
# A193142: Primes which are the sum of 5 distinct positive squares.

Source: https://oeis.org/A193142
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A193142 (Vladimir Joseph Stephan Orlovsky, Jul 16
2011): a(n) = prime(n+32) for n > 13.

Conventions:
* The sequence has offset 1 (data 79, 103, 127, 131, 139, 151, 157, 163, 167, 179, 181, 191, ...).
* `S5 p` says that p is a prime which is the sum of the squares of 5 distinct positive integers (a
  5-element finset of positive natural numbers).
* a(n) is the n-th such prime in increasing order, i.e. `Nat.nth S5 (n - 1)` (`Nat.nth` is
  0-indexed), and prime(n+32) is `Nat.nth Nat.Prime (n + 31)`.
-/

namespace OMA.S_oeis_a193142

/-- p is a prime which is the sum of 5 distinct positive squares. -/
def S5 (p : ℕ) : Prop :=
  p.Prime ∧ ∃ s : Finset ℕ, s.card = 5 ∧ (∀ x ∈ s, 0 < x) ∧ ∑ x ∈ s, x ^ 2 = p

/-- The conjecture recorded in A193142. -/
theorem main : ∀ n : ℕ, 13 < n → Nat.nth S5 (n - 1) = Nat.nth Nat.Prime (n + 31) := by
  sorry

end OMA.S_oeis_a193142

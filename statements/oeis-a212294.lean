import Mathlib

/-!
# OEIS A212294: sums of distinct twin primes

Source: https://oeis.org/A212294 (Charles R Greathouse IV, June 21, 2012).
Formalization: @iancbaer.
Source text/data: OEIS Foundation, CC BY-SA 4.0.

A twin prime here is either member of a prime pair at distance two, not
just the smaller member. Finsets enforce distinctness and allow the empty
sum. OEIS uses offset 1: a(1) = 0, a(2) = 3, ..., a(6) = 10.
Nat.nth uses offset 0, so a(n) is Nat.nth isSum (n - 1).
The source conjectures a(n) = n + 4 for every n > 5.

This is a statement submission, not a claimed proof. The site's statement
workflow requires exactly one sorry, in main, pending human review.
-/

namespace OMA.S_oeis_a212294

def isTwinPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ (Nat.Prime (p + 2) ∨ Nat.Prime (p - 2))

def isSum (m : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ p ∈ s, isTwinPrime p) ∧ ∑ p ∈ s, p = m

noncomputable def a (n : ℕ) : ℕ := Nat.nth isSum (n - 1)

theorem main : ∀ n : ℕ, 5 < n → a n = n + 4 := by
  sorry

end OMA.S_oeis_a212294

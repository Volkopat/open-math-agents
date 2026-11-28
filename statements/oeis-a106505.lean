import Mathlib

/-!
# A106505: Ordered and uniqued length of side common to the two angles, one being the double of the other, of a primitive integer-sided triangle.

Source: https://oeis.org/A106505
Credit: @agchua

Formula line of A106505 (conjecture by Ralf Stephan, Nov 16 2010):
  Conjecture: for n>2, a(n+5) = a(n) + 8.

Offset 1, data 5, 7, 9, 11, 13, 15, 16, 17, 19, 21, 23, 24, ... By the entry's formula line the
terms are the values s^2 - r^2 where r < s < 2r and (r, s) = 1 (the side common to the angles A
and 2A of the primitive triangle with sides r^2, r*s, s^2 - r^2), listed in increasing order
without repetition. IsTerm m says that m is such a value, and a(n) = Nat.nth IsTerm (n - 1) is
the n-th smallest one. The conjecture is stated for n > 2, as in the entry.
-/

namespace OMA.S_oeis_a106505

/-- m is a value s^2 - r^2 with r < s < 2r and gcd(r, s) = 1. -/
def IsTerm (m : ℕ) : Prop :=
  ∃ r s : ℕ, r < s ∧ s < 2 * r ∧ Nat.Coprime r s ∧ m = s ^ 2 - r ^ 2

/-- a(n) is the n-th smallest term (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- The conjecture: a(n+5) = a(n) + 8 for every n > 2. -/
theorem main : ∀ n : ℕ, 2 < n → a (n + 5) = a n + 8 := by
  sorry

end OMA.S_oeis_a106505

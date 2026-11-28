import Mathlib

/-!
# A181666: Numbers whose odd part is of the form (4^k-1)/3.

Source: https://oeis.org/A181666
Credit: @agchua

Comment of A181666 (unsigned; the entry is by Ralf Stephan, Nov 18 2010):
  Also, terms of A023758 divisible by 3, divided by 3 (conjectured).
A023758: Numbers of the form 2^i - 2^j with i >= j (offset 1; its first term is 0, from i = j).
A181666 has offset 1 and first term 1. The odd part of m >= 1 (A000265) is m / 2^v, where 2^v is
the largest power of 2 that divides m. The conjecture says that the terms of A181666 are exactly
the numbers x/3 with x a term of A023758 divisible by 3. The term x = 0 of A023758 is divisible
by 3 but gives 0, which has no odd part and is not a term of A181666 (data 1, 2, 4, 5, 8, ...);
so x ranges over the positive terms of A023758.
-/

namespace OMA.S_oeis_a181666

/-- The odd part of m (A000265): m divided by the largest power of 2 that divides m. -/
noncomputable def oddPart (m : ℕ) : ℕ := m / 2 ^ (Nat.factorization m 2)

/-- m is a term of A181666: m >= 1 and the odd part of m is (4^k - 1)/3 for some k. -/
def IsA181666 (m : ℕ) : Prop := 0 < m ∧ ∃ k : ℕ, oddPart m = (4 ^ k - 1) / 3

/-- x is a term of A023758: x = 2^i - 2^j for some i >= j. -/
def IsA023758 (x : ℕ) : Prop := ∃ i j : ℕ, j ≤ i ∧ x = 2 ^ i - 2 ^ j

/-- The conjecture: the terms of A181666 are exactly the numbers x/3, where x is a positive term
of A023758 that is divisible by 3. -/
theorem main : ∀ m : ℕ, IsA181666 m ↔ ∃ x : ℕ, IsA023758 x ∧ 0 < x ∧ 3 ∣ x ∧ m = x / 3 := by
  sorry

end OMA.S_oeis_a181666

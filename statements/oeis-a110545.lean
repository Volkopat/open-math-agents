import Mathlib

/-!
# A110545: a(n) is smallest positive integer m such that n divides either the numerator or the denominator of the (reduced) fraction H(m) = Sum_{k=1..m} 1/k.

Source: https://oeis.org/A110545
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A110545 (Leroy Quet, Sep 11 2005): a(n) <= n for all
positive n.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 4, 4, 3, 6, 8, 9, 5, 3, 4, ...).
* H(m) = Sum_{k=1..m} 1/k is the Mathlib harmonic number `harmonic m : ℚ`; the numerator and
  denominator of the reduced fraction are `Rat.num` (a positive integer here, taken as a natural
  number with `Int.natAbs`) and `Rat.den`.
* a(n) is the smallest positive integer m such that n divides the numerator or the denominator of
  H(m). The claim a(n) <= n (which includes that a(n) exists) is stated as: there is such an m
  with 0 < m <= n; this is the same as a(n) <= n for the least such m.
-/

namespace OMA.S_oeis_a110545

/-- The conjecture recorded in A110545: the least m > 0 such that n divides the numerator or the
denominator of H(m) is at most n. -/
theorem main : ∀ n : ℕ, 0 < n →
    ∃ m : ℕ, 0 < m ∧ m ≤ n ∧ (n ∣ (harmonic m).num.natAbs ∨ n ∣ (harmonic m).den) := by
  sorry

end OMA.S_oeis_a110545

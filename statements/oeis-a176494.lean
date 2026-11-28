import Mathlib

/-!
# A176494: Least m >= 1 for which |2^m - prime(n)| is prime.

Source: https://oeis.org/A176494
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A176494 (Vladimir Shevelev, Apr 19 2010, Aug 15 2010):
For every odd prime p, the sequence {|2^n - p|} contains at least one prime.

Conventions:
* The sequence has offset 2 (data 3, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 2, ...).
* The sequence |2^m - p| is indexed by m >= 1, as in the OEIS name (least m >= 1 for which |2^m -
  prime(n)| is prime). The difference is computed in `ℤ` and `Int.natAbs` is its absolute value.
-/

namespace OMA.S_oeis_a176494

/-- The conjecture recorded in A176494. -/
theorem main : ∀ p : ℕ, p.Prime → Odd p →
    ∃ m : ℕ, 1 ≤ m ∧ (Int.natAbs ((2 : ℤ) ^ m - p)).Prime := by
  sorry

end OMA.S_oeis_a176494

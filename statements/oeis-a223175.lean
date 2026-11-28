import Mathlib

/-!
# A223175: Smallest prime q such that 2n+1 = p + 8*q for some odd prime p, or 0 if no such prime exists.

Source: https://oeis.org/A223175
Credit: @EtienneLefranc

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a223175

/-- The conjecture stated in A223175: except m = 25 and 49, all odd numbers m > 17 are of
the form m = p + 8*q where p and q are prime numbers. -/

theorem main :
    ∀ m : ℕ, Odd m → 17 < m → m ≠ 25 → m ≠ 49 →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p + 8 * q := by
  sorry

end OMA.S_oeis_a223175


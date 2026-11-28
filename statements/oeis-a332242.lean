import Mathlib

/-!
# A332242: Numbers k such that k! has exactly k nonzero decimal digits.

Source: https://oeis.org/A332242
Credit: @luciusacarr

Data: 1, 48, 49, 53, 54, 57. No other terms < 100000.

Conjecture (from the entry): these 6 terms are the only terms of the sequence, i.e., there are no
terms larger than 57. `main` states it.

Reading of the source:
* The nonzero decimal digits of `k!` are the nonzero entries of `Nat.digits 10 (k !)`; they are
  counted with multiplicity (48! has 48 nonzero digits).
* `k` ranges over the positive integers (offset 1).
* "These 6 terms are the only terms" is stated as: `k!` has exactly `k` nonzero decimal digits if
  and only if `k` is one of 1, 48, 49, 53, 54, 57.
-/

namespace OMA.S_oeis_a332242

/-- The number of nonzero decimal digits of `n`. -/
def nonzeroDigits (n : ℕ) : ℕ := ((Nat.digits 10 n).filter (· ≠ 0)).length

theorem main :
    -- 1, 48, 49, 53, 54 and 57 are the only terms.
    ∀ k : ℕ, 1 ≤ k → (nonzeroDigits k.factorial = k ↔ k ∈ ({1, 48, 49, 53, 54, 57} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a332242

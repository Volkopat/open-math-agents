import Mathlib

/-!
# A309129: Numbers k such that -k is a quadratic nonresidue modulo all odd primes p <= sqrt(k) which do not divide k.

Source: https://oeis.org/A309129
Credit: @azmiozgen

Conjecture (from the entry): 1848 is the last term of this sequence.

Formalization notes:
* For an odd prime p not dividing k, -k is a quadratic nonresidue mod p iff -k is not a square in
  ZMod p. "p ≤ sqrt(k)" is p * p ≤ k.
* Stated as: 1848 is a term and no k > 1848 is a term.
* Controls (computed): the terms below 300000 number 84, the last three being 1365, 1467, 1848.
-/

namespace OMA.S_oeis_a309129

/-- `k` is a term of A309129. -/
def IsTerm (k : ℕ) : Prop :=
  0 < k ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → p * p ≤ k → ¬ p ∣ k → ¬ IsSquare ((-(k : ℤ) : ZMod p))

/-- The conjecture of the entry. -/
theorem main :
    IsTerm 1848 ∧ ∀ k : ℕ, 1848 < k → ¬ IsTerm k := by
  sorry

end OMA.S_oeis_a309129

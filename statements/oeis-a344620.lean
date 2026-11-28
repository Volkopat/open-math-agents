import Mathlib

/-!
# A344620: Pythagorean triples (2a, a^2-1, a^2+1) of quadratic residues

Source: https://oeis.org/A344620
Credit: @coleman415

The sequence (Zhi-Wei Sun) lists the primes `p` such that there is no positive integer `a` with
`2*a`, `a^2-1` and `a^2+1` not only smaller than `p` but also quadratic residues modulo `p`.
The entry records: *Conjecture: No term is greater than 827. In other words, for any prime
p > 828, there is a Pythagorean triple (2*a, a^2-1, a^2+1) with 2*a, a^2-1 and a^2+1 in the set
{0 < r < p: r is a quadratic residue modulo p}.*

Conventions:
- The set of quadratic residues is `{0 < r < p : r is a square modulo p}`, as written in the
  entry; `0` is excluded. So `a = 1` (where `a^2 - 1 = 0`) is never a witness, and for `a ≥ 1`
  the natural-number subtraction `a^2 - 1` is the integer difference.
-/

namespace OMA.S_oeis_a344620

/-- `r` belongs to `{0 < r < p : r is a quadratic residue modulo p}`. -/
def IsSmallResidue (p r : ℕ) : Prop := 0 < r ∧ r < p ∧ IsSquare (r : ZMod p)

/-- The conjecture of OEIS A344620. -/
theorem main :
    ∀ p : ℕ, p.Prime → 828 < p →
      ∃ a : ℕ, 0 < a ∧ IsSmallResidue p (2 * a) ∧ IsSmallResidue p (a ^ 2 - 1) ∧
        IsSmallResidue p (a ^ 2 + 1) := by
  sorry

end OMA.S_oeis_a344620

import Mathlib

/-!
Source: OEIS A138217 and A137576. The conjecture of infinitely many composite
members holds by considering powers of 3. The stronger assertion in the
comment about all odd prime powers has a counterexample at the square of the
Wieferich prime 1093.
-/

namespace OMA.S_oeis_a138217

/-- The multiplicative order of 2 modulo `d`. -/
noncomputable def ordTwo (d : ℕ) : ℕ := orderOf (2 : ZMod d)

/-- A137576((n-1)/2) - 1 for odd positive `n`, using the OEIS divisor sum. -/
noncomputable def excess (n : ℕ) : ℕ :=
  ordTwo n * ((∑ d ∈ n.divisors, d.totient / ordTwo d) - 1)

/-- Membership in A138217. -/
def IsMember (n : ℕ) : Prop := Odd n ∧ n.totient ∣ excess n

/-- The A138217 infinitude conjecture, its power-of-3 family, and the
exception to the stronger all-odd-prime-powers assertion. -/
theorem main :
    {n : ℕ | 1 < n ∧ ¬ n.Prime ∧ IsMember n}.Infinite ∧
    (∀ k : ℕ, excess (3 ^ k) = k * (3 ^ k : ℕ).totient) ∧
    ¬ IsMember (1093 ^ 2) := by
  sorry

end OMA.S_oeis_a138217

import Mathlib

/-!
# OEIS A275021: Pairs of primes p, p+4 such that p-2 and p+6 are composite

Source: https://oeis.org/A275021
Credit: @unserus

OEIS: "Conjecture: the sequence has infinitely many terms and the sum of their
reciprocals converges." and (Charles R Greathouse IV, Nov 20 2016): "The second
half of the conjecture is correct. The first half is true on Dickson's
conjecture."

The sequence lists both members of each pair `p, p + 4` of primes with `p - 2`
and `p + 6` composite. It is infinite exactly when there are infinitely many
such `p`, so only the open first half is stated: the set of such `p` is
infinite. "Composite" is `1 < m ∧ ¬ m.Prime`.
-/

namespace OMA.S_oeis_a275021

/-- `m` is composite. -/
def IsComposite (m : ℕ) : Prop := 1 < m ∧ ¬ m.Prime

/-- The smaller members `p` of the pairs in A275021. -/
def a275021Lower : Set ℕ :=
  {p | p.Prime ∧ (p + 4).Prime ∧ IsComposite (p - 2) ∧ IsComposite (p + 6)}

/-- There are infinitely many primes `p` with `p + 4` prime and `p - 2`, `p + 6`
composite. -/
theorem main : a275021Lower.Infinite := by
  sorry

end OMA.S_oeis_a275021

import Mathlib.Order.Lattice.Nat

/-!
# Greedy sums that are Jacobsthal numbers

Source: https://oeis.org/A215095
Credit: @jatin6

Alex Ratushnyak defined the sequence. David Scambler conjectured its
ordinary generating function on August 6, 2012.
-/

namespace OMA.S_oeis_a215095

def jac : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => jac (n+1) + 2 * jac n

/-- The least number above the previous term whose sum with the older term
is a Jacobsthal number. -/
noncomputable def nextTerm (older previous : ℕ) : ℕ :=
  sInf {k : ℕ | previous < k ∧ ∃ i : ℕ, k + older = jac i}

noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => nextTerm (a n) (a (n+1))

/-- The coefficients after multiplying a series by 1-X-X²-X³-2X⁴. -/
def denominatorProduct (u : ℕ → ℤ) : ℕ → ℤ
  | 0 => u 0
  | 1 => u 1 - u 0
  | 2 => u 2 - u 1 - u 0
  | 3 => u 3 - u 2 - u 1 - u 0
  | n + 4 => u (n+4) - u (n+3) - u (n+2) - u (n+1) - 2 * u n

/-- The ordinary generating function is (X+2X²)/(1-X-X²-X³-2X⁴).
Equality after multiplying by the denominator is coefficientwise. -/
theorem main : ∀ n : ℕ, denominatorProduct (fun k => (a k : ℤ)) n =
    (if n = 1 then 1 else if n = 2 then 2 else 0) := by
  sorry

end OMA.S_oeis_a215095

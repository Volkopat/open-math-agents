import Mathlib

/-!
# Dowe's conjecture on the parity of Erdős–Woods numbers

Source: https://oeis.org/A111042.
A length d > 1 is an Erdős–Woods number if some integer interval
[a,a+d], with a > 1, has the following property: every integer in
it has a common divisor greater than one with at least one endpoint.
Dowe conjectured that every such length is even.
-/

namespace OMA.S_oeis_a111042

def Woods (d : ℕ) : Prop :=
  1 < d ∧ ∃ a : ℕ, 1 < a ∧ ∀ i ≤ d,
    1 < Nat.gcd a (a+i) ∨ 1 < Nat.gcd (a+d) (a+i)

theorem main : ∀ d : ℕ, Woods d → Even d := by
  sorry

end OMA.S_oeis_a111042
